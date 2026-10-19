"""Morning weather -> Telegram: what to bring today (umbrella, sunscreen, mask).

Telegram commands:
  /location Seoul    set your location (city name in any language, e.g. Tokyo, 울산, "Portland, US")
  /time 5:00         set the daily message time (local time of your location; also 7am, 18:30, 0630)
  /now               send today's forecast right now
  /settings          show your location and time

Data: Open-Meteo (free, no API key) for forecast, UV index and air quality.
Run periodically by GitHub Actions: handle commands -> send the daily message if it's time -> save state.
The repo is public, so the state (your location) is saved encrypted in state.enc with the STATE_KEY secret,
and logs never show your location or messages.
No external packages (Python standard library only).
"""
import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

TOKEN = os.environ["TG_TOKEN"].strip()
CHAT_ID = os.environ["TG_CHAT_ID"].strip()
STATE_KEY = (os.environ.get("STATE_KEY") or "").strip()  # without it, state is saved unencrypted in state.json
PLAIN_STATE = Path("state.json")
SECRET_STATE = Path("state.enc")
MENU_VERSION = 1  # bump when COMMANDS change so Telegram's menu gets refreshed
DEFAULT_TIME = "05:00"
SEND_WINDOW_HOURS = 3  # if runs were delayed past this, skip the day instead of sending a stale "morning" message
DAY_HOURS = range(6, 24)  # hours that count for "today" (rain at 3am doesn't need an umbrella)

GEO_URL = "https://geocoding-api.open-meteo.com/v1/search"
FORECAST_URL = "https://api.open-meteo.com/v1/forecast"
AIR_URL = "https://air-quality-api.open-meteo.com/v1/air-quality"

HELP = (
    "Commands:\n"
    "/location CITY — set your location (any language: Seoul, 울산, Tokyo)\n"
    "   Same name in many countries? Add the country: /location Portland, US\n"
    "/time HH:MM — daily message time (e.g. /time 5:00, /time 7am)\n"
    "/now — today's forecast right now\n"
    "/settings — your location and time\n\n"
    "Every morning you get what to bring: ☔ umbrella · 🧴 sunscreen · 😷 mask."
)
COMMANDS = [
    {"command": "location", "description": "Set location: /location Seoul"},
    {"command": "time", "description": "Set daily time: /time 5:00"},
    {"command": "now", "description": "Today's forecast now"},
    {"command": "settings", "description": "Show location and time"},
]

# Korean air quality standards (µg/m³): good / normal / bad / very bad
PM25_LEVELS = [(15, "good"), (35, "normal"), (75, "bad"), (float("inf"), "very bad")]
PM10_LEVELS = [(30, "good"), (80, "normal"), (150, "bad"), (float("inf"), "very bad")]
# WHO UV index scale
UV_LEVELS = [(2, "low"), (5, "moderate"), (7, "high"), (10, "very high"), (float("inf"), "extreme")]


def why(e):
    """Short error text for the public log: the error type (and HTTP code), never URLs or places."""
    return f"{type(e).__name__} {e.code}" if isinstance(e, urllib.error.HTTPError) else type(e).__name__


# ---------- HTTP ----------
def get_json(url, **params):
    req = urllib.request.Request(f"{url}?{urllib.parse.urlencode(params)}", headers={"User-Agent": "weather-alert bot"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def tg(method, **params):
    url = f"https://api.telegram.org/bot{TOKEN}/{method}"
    data = urllib.parse.urlencode(params).encode()
    with urllib.request.urlopen(url, data=data, timeout=30) as r:
        return json.load(r)


def send(text):
    tg("sendMessage", chat_id=CHAT_ID, text=text[:4000], disable_web_page_preview="true")


# ---------- Location ----------
def find_place(query):
    """'Seoul' / '울산' / 'Portland, US' -> best matching place dict, or None."""
    name, _, country = (x.strip() for x in query.partition(","))
    results = get_json(GEO_URL, name=name, count=10, language="en", format="json").get("results") or []
    if country:
        c = country.lower()
        results = [r for r in results if c in (r.get("country_code", "").lower(), r.get("country", "").lower())]
    if not results:
        return None
    # Results come ranked by relevance; prefer a city over a district or a mountain with the same name.
    best = max(results[:5], key=lambda r: (r.get("feature_code", "").startswith("PPL"), r.get("population") or 0))
    return {
        "name": best["name"],
        "region": best.get("admin1", ""),
        "country": best.get("country", ""),
        "lat": best["latitude"],
        "lon": best["longitude"],
        "tz": best.get("timezone") or "UTC",
    }


def place_label(p):
    parts = [p["name"]] + [x for x in (p.get("region"), p.get("country")) if x and x != p["name"]]
    return ", ".join(parts)


def parse_time(s):
    """'5', '0500', '5:00', '17:30', '7am', '6:30pm' -> 'HH:MM'. Raises ValueError if it can't be read."""
    m = re.fullmatch(r"(\d{1,2})(?::?(\d{2}))?\s*(am|pm)?", s.strip().lower())
    if not m:
        raise ValueError(s)
    h, mnt, ampm = int(m.group(1)), int(m.group(2) or 0), m.group(3)
    if ampm == "pm" and h < 12:
        h += 12
    if ampm == "am" and h == 12:
        h = 0
    if not (0 <= h < 24 and 0 <= mnt < 60):
        raise ValueError(s)
    return f"{h:02d}:{mnt:02d}"


# ---------- Forecast ----------
def level(value, levels):
    value = round(value)  # scales use whole numbers: UV 7.4 is "high" (6-7), not "very high"
    return next(name for limit, name in levels if value <= limit)


def hour_span(hours):
    """[15, 16, 17] -> '15:00–18:00'; scattered hours -> first–last."""
    return f"{hours[0]:02d}:00–{hours[-1] + 1:02d}:00"


def today_brief(place):
    """The morning message: what to bring, then temperatures."""
    tz = ZoneInfo(place["tz"])
    today = datetime.now(tz).date().isoformat()
    fc = get_json(FORECAST_URL, latitude=place["lat"], longitude=place["lon"], timezone=place["tz"], past_days=1, forecast_days=1,
                  hourly="precipitation_probability,precipitation,snowfall,uv_index",
                  daily="temperature_2m_max,temperature_2m_min")
    hourly = fc["hourly"]
    col = lambda k: hourly.get(k) or [None] * len(hourly["time"])  # some places lack a variable -> treat as unknown
    pct, mm, snow, uvi = col("precipitation_probability"), col("precipitation"), col("snowfall"), col("uv_index")
    rows = [  # (hour, rain %, rain mm, snow cm, uv) for today's daytime
        (int(t[11:13]), pct[i], mm[i], snow[i], uvi[i])
        for i, t in enumerate(hourly["time"]) if t.startswith(today) and int(t[11:13]) in DAY_HOURS
    ]
    bring, notes = [], []

    # ☔ Rain / snow
    rainy = [h for h, pct, mm, _, _ in rows if (pct or 0) >= 50 or (mm or 0) >= 0.5]
    maybe = [h for h, pct, _, _, _ in rows if 30 <= (pct or 0) < 50]
    snowy = [h for h, _, _, cm, _ in rows if (cm or 0) > 0]
    top = max((pct or 0 for _, pct, _, _, _ in rows), default=0)
    if snowy:
        bring.append(f"❄️ Snow — {hour_span(snowy)}, take an umbrella and good shoes")
    elif rainy:
        bring.append(f"☔ Umbrella — rain likely {hour_span(rainy)} (up to {top}%)")
    elif maybe:
        bring.append(f"🌂 Small umbrella just in case — {top}% chance around {hour_span(maybe)}")

    # 🧴 Sunscreen
    uv = [(h, u) for h, _, _, _, u in rows if u is not None]
    peak = max((u for _, u in uv), default=0)
    if peak >= 6:
        strong = [h for h, u in uv if u >= 6]
        bring.append(f"🧴 Sunscreen — UV {level(peak, UV_LEVELS)} ({peak:.0f}), strongest {hour_span(strong)}")
    elif peak >= 3:
        bring.append(f"🧴 Sunscreen if you're outside long — UV {level(peak, UV_LEVELS)} ({peak:.0f})")

    # 😷 Fine dust
    try:
        air = get_json(AIR_URL, latitude=place["lat"], longitude=place["lon"], timezone=place["tz"], forecast_days=1,
                       hourly="pm10,pm2_5")["hourly"]
        day = [i for i, t in enumerate(air["time"]) if t.startswith(today) and int(t[11:13]) in DAY_HOURS]
        pm25 = max((air["pm2_5"][i] or 0 for i in day), default=0)
        pm10 = max((air["pm10"][i] or 0 for i in day), default=0)
        worst = max(level(pm25, PM25_LEVELS), level(pm10, PM10_LEVELS), key=[n for _, n in PM25_LEVELS].index)
        if worst in ("bad", "very bad"):
            bring.append(f"😷 Mask — fine dust {worst} (PM2.5 {pm25:.0f} · PM10 {pm10:.0f})")
        else:
            notes.append(f"🌫 Air {worst}")
    except Exception as e:  # air data missing for some places -> the rest of the message still goes out
        print(f"air quality failed: {why(e)}")

    # 🌡 Temperature (vs yesterday)
    daily = fc["daily"]
    hi, lo = daily["temperature_2m_max"][-1], daily["temperature_2m_min"][-1]
    temp = f"🌡 {hi:.0f}° / {lo:.0f}°"
    if len(daily["time"]) > 1 and daily["temperature_2m_max"][0] is not None:
        diff = hi - daily["temperature_2m_max"][0]
        if diff <= -3:
            temp += f" ({-diff:.0f}° colder than yesterday — bring a layer)"
        elif diff >= 3:
            temp += f" ({diff:.0f}° warmer than yesterday)"
    notes.insert(0, temp)

    head = f"☀️ {datetime.now(tz):%a %m/%d} · {place['name']}"
    body = "\n".join(bring) if bring else "✅ Nothing extra to bring today"
    return f"{head}\n\n{body}\n\n" + "\n".join(notes)


# ---------- Telegram commands ----------
def handle_commands(state):
    if state.get("menu_version") != MENU_VERSION:  # refresh Telegram's command menu
        tg("setMyCommands", commands=json.dumps(COMMANDS))
        state["menu_version"] = MENU_VERSION
    updates = tg("getUpdates", offset=state.get("offset", 0), timeout=0).get("result", [])
    print(f"{len(updates)} new Telegram message(s)")
    for u in updates:
        state["offset"] = u["update_id"] + 1
        msg = u.get("message") or {}
        # The repo (and its Actions logs) is public: never log chat ids or message text.
        if str(msg.get("chat", {}).get("id")) != CHAT_ID:
            print("  ignored a message from another chat (doesn't match TG_CHAT_ID)")
            continue
        text = (msg.get("text") or "").strip()
        if not text:
            continue
        cmd, _, arg = text.partition(" ")
        try:
            run_command(state, cmd.lower().split("@")[0], arg.strip())
        except Exception as e:
            print(f"command failed: {why(e)}")
            send(f"⚠️ Something went wrong ({why(e)}). Try again in a few minutes.")


def run_command(state, cmd, arg):
    place = state.get("place")
    if cmd == "/location" and arg:
        found = find_place(arg)
        if not found:
            send(f"❔ Couldn't find \"{arg}\". Try the English name or add the country, e.g. /location Portland, US")
            return
        state["place"] = found
        state.pop("last_sent", None)
        send(f"📍 Location set: {place_label(found)}\n"
             f"Daily message at {state.get('time', DEFAULT_TIME)} ({found['tz']} time).\n\n"
             "Wrong place? Add the country: /location Name, Country\nSee today now: /now")

    elif cmd == "/time" and arg:
        try:
            state["time"] = parse_time(arg)
        except ValueError:
            send("Time must look like 5:00, 0630, 7am or 18:30")
            return
        state.pop("last_sent", None)
        where = f" ({place['tz']} time)" if place else ""
        send(f"⏰ Daily message time set: {state['time']}{where}")

    elif cmd == "/now":
        if not place:
            send("📍 Set your location first: /location Seoul")
            return
        send(today_brief(place))

    elif cmd == "/settings":
        where = place_label(place) if place else "not set — /location Seoul"
        send(f"⚙️ Settings\n📍 Location: {where}\n⏰ Daily message: {state.get('time', DEFAULT_TIME)}")

    else:
        intro = "" if place else "👋 First, set your location: /location Seoul\n\n"
        send(intro + HELP)


# ---------- Daily message ----------
def send_daily(state):
    place = state.get("place")
    if not place:
        return
    now = datetime.now(ZoneInfo(place["tz"]))
    hh, mm = map(int, state.get("time", DEFAULT_TIME).split(":"))
    due = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
    today = now.date().isoformat()
    if state.get("last_sent") == today or now < due:
        return
    if now - due <= timedelta(hours=SEND_WINDOW_HOURS):
        send(today_brief(place))
    state["last_sent"] = today  # also marks a skipped (too late) day, so it isn't retried every run


# ---------- Encrypted state ----------
# Standard library only: SHA-256 keystream (counter mode) + HMAC-SHA256 to detect a wrong key or tampering.
def state_keys():
    k = hashlib.sha256(STATE_KEY.encode()).digest()
    return hashlib.sha256(b"enc" + k).digest(), hashlib.sha256(b"mac" + k).digest()


def keystream_xor(key, nonce, data):
    stream = b"".join(hashlib.sha256(key + nonce + i.to_bytes(8, "big")).digest() for i in range((len(data) + 31) // 32))
    return bytes(a ^ b for a, b in zip(data, stream))


def encrypt(data):
    enc_key, mac_key = state_keys()
    nonce = secrets.token_bytes(16)
    body = nonce + keystream_xor(enc_key, nonce, data)
    return base64.b64encode(body + hmac.new(mac_key, body, hashlib.sha256).digest()).decode() + "\n"


def decrypt(text):
    enc_key, mac_key = state_keys()
    raw = base64.b64decode(text)
    body, tag = raw[:-32], raw[-32:]
    if not hmac.compare_digest(tag, hmac.new(mac_key, body, hashlib.sha256).digest()):
        raise SystemExit("state.enc can't be opened: the STATE_KEY secret is wrong or was changed")
    return keystream_xor(enc_key, body[:16], body[16:])


def load_state():
    if SECRET_STATE.exists():
        if not STATE_KEY:  # never start over just because the secret is missing
            raise SystemExit("state.enc exists but the STATE_KEY secret is missing")
        return json.loads(decrypt(SECRET_STATE.read_text()))
    if PLAIN_STATE.exists():
        return json.loads(PLAIN_STATE.read_text())
    return {"offset": 0}


def save_state(state):
    data = (json.dumps(state, indent=1, ensure_ascii=False, sort_keys=True) + "\n").encode()
    if not STATE_KEY:
        PLAIN_STATE.write_bytes(data)
        return
    # Encryption is random each time, so only rewrite when something changed (no commit every run).
    if not SECRET_STATE.exists() or decrypt(SECRET_STATE.read_text()) != data:
        SECRET_STATE.write_text(encrypt(data))
    PLAIN_STATE.unlink(missing_ok=True)


def main():
    state = load_state()
    handle_commands(state)
    try:
        send_daily(state)
    except Exception as e:  # weather service down -> try again next run (last_sent isn't set)
        print(f"daily message failed: {why(e)}")
    # guarantees a commit at least monthly, so GitHub doesn't disable the schedule after 60 idle days
    state["heartbeat"] = time.strftime("%Y-%m")
    save_state(state)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # the default traceback could print a place or URL in the public log
        raise SystemExit(f"run failed: {why(e)}")
