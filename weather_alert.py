"""Morning weather -> Telegram: what to bring today (umbrella, sunscreen, mask),
plus an update during the day if rain, snow or fine dust shows up that the morning message didn't mention.

Telegram commands:
  /location Seoul    set your location (city name in English or the local language, e.g. Tokyo, "Portland, US")
  /time 5:00         set the daily message time (local time of your location; also 7am, 18:30, 0630)
  /now               send today's forecast right now
  /settings          show your location and time

Data: Open-Meteo (free, no API key) for forecast, UV index and air quality.
Run periodically by GitHub Actions: handle commands -> daily message -> hourly update check -> save state.
The repo is public, so the state (your location and settings) is saved encrypted in state.enc with the STATE_KEY secret,
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
UPDATE_UNTIL_HOUR = 21  # hourly "weather got worse" checks stop at this local hour
SUNSCREEN_UV = 3  # UV index from which sunscreen is suggested (WHO: 3+ = moderate, use protection)
# Outfit from the coldest / warmest "feels like" temperature of the day, for the clothes actually owned:
# light padded jacket, windbreaker, short sleeves
PADDED_BELOW = 10  # feels-like at or below -> light padded jacket
WINDBREAKER_BELOW = 19  # feels-like at or below -> windbreaker
SHORT_SLEEVES_FROM = 25  # warmest feels-like at or above -> short sleeves are fine
WINDY_GUSTS = 40  # km/h; on a padded-jacket day, add the windbreaker on top
# Comfort line (shown only on notable days), from internationally used indices:
# Heat Index (US National Weather Service, Rothfusz): 27+ caution, 32+ extreme caution, 41+ danger (°C)
HEAT_CAUTION, HEAT_EXTREME, HEAT_DANGER = 27, 32, 41
# Wind chill (2001 joint US/Canada index): -10 or below uncomfortable/risk if outside long, -28 or below frostbite risk
CHILL_COLD, CHILL_FROSTBITE = -10, -28
RAIN_NONE, RAIN_MAYBE, RAIN_YES, RAIN_SNOW = 0, 1, 2, 3  # ordered: a higher value is worse

GEO_URL = "https://geocoding-api.open-meteo.com/v1/search"
FORECAST_URL = "https://api.open-meteo.com/v1/forecast"
AIR_URL = "https://air-quality-api.open-meteo.com/v1/air-quality"

HELP = (
    "Commands:\n"
    "/location CITY — set your location (English or local name: Seoul, Tokyo)\n"
    "   Same name in many countries? Add the country: /location Portland, US\n"
    "/time HH:MM — daily message time (e.g. /time 5:00, /time 7am)\n"
    "/now — today's forecast right now\n"
    "/settings — your location and time\n\n"
    "Every morning you get what to bring: ☔ umbrella · 🧴 sunscreen · 😷 mask.\n"
    "If rain, snow or fine dust shows up later in the day, you get an update."
)
COMMANDS = [
    {"command": "location", "description": "Set location: /location Seoul"},
    {"command": "time", "description": "Set daily time: /time 5:00"},
    {"command": "now", "description": "Today's forecast now"},
    {"command": "settings", "description": "Show location and time"},
]

# WHO Air Quality Guidelines 2021, 24-hour means (µg/m³): guideline level, and interim target 3 above which a mask is
# suggested (WHO doesn't name categories, so the message shows how many times the guideline the air is)
WHO_PM25, WHO_PM10 = 15, 45
MASK_PM25, MASK_PM10 = 37.5, 75
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
    """'Seoul' / a local-language name / 'Portland, US' -> best matching place dict, or None."""
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
    """[15, 16, 17] -> '15:00–18:00'; scattered hours -> first–last; 12+ hours -> 'most of the day'."""
    return "most of the day" if len(hours) >= 12 else f"{hours[0]:02d}:00–{hours[-1] + 1:02d}:00"


def fetch_forecast(place):
    """(hourly forecast, daily temperatures, hourly air quality or None) from Open-Meteo, in local time."""
    fc = get_json(FORECAST_URL, latitude=place["lat"], longitude=place["lon"], timezone=place["tz"], past_days=1, forecast_days=1,
                  hourly="precipitation_probability,precipitation,snowfall,uv_index,apparent_temperature,wind_gusts_10m,"
                         "temperature_2m,relative_humidity_2m,wind_speed_10m",
                  daily="temperature_2m_max,temperature_2m_min")
    try:
        air = get_json(AIR_URL, latitude=place["lat"], longitude=place["lon"], timezone=place["tz"], forecast_days=1,
                       hourly="pm10,pm2_5")["hourly"]
    except Exception as e:  # air data missing for some places -> the rest still works
        print(f"air quality failed: {why(e)}")
        air = None
    return fc["hourly"], fc["daily"], air


def assess(place, hours):
    """What to bring for the given hours of today, as plain values (so morning and later checks can be compared)."""
    today = datetime.now(ZoneInfo(place["tz"])).date().isoformat()
    hourly, daily, air = fetch_forecast(place)
    col = lambda data, k: data.get(k) or [None] * len(data["time"])  # some places lack a variable -> treat as unknown
    pct, mm, snow, uvi = (col(hourly, k) for k in ("precipitation_probability", "precipitation", "snowfall", "uv_index"))
    rows = [(int(t[11:13]), pct[i] or 0, mm[i] or 0, snow[i] or 0, uvi[i])  # (hour, rain %, rain mm, snow cm, uv)
            for i, t in enumerate(hourly["time"]) if t.startswith(today) and int(t[11:13]) in hours]
    a = {"rain": RAIN_NONE, "rain_hours": [], "top": max((r[1] for r in rows), default=0),
         "uv": max((r[4] for r in rows if r[4] is not None), default=0), "uv_hours": [], "dust": "", "pm25": 0, "pm10": 0}
    snowy = [h for h, _, _, cm, _ in rows if cm > 0]
    rainy = [h for h, p, mm_, _, _ in rows if p >= 50 or mm_ >= 0.5]
    maybe = [h for h, p, _, _, _ in rows if 30 <= p < 50]
    for kind, found in ((RAIN_SNOW, snowy), (RAIN_YES, rainy), (RAIN_MAYBE, maybe)):
        if found:
            a["rain"], a["rain_hours"] = kind, found
            break
    a["uv_hours"] = [h for h, *_, u in rows if u is not None and round(u) >= SUNSCREEN_UV]
    if air:
        day = [i for i, t in enumerate(air["time"]) if t.startswith(today) and int(t[11:13]) in hours]
        mean = lambda xs: sum(xs) / len(xs) if xs else 0  # WHO guidelines are 24-hour means, not hourly peaks
        a["pm25"] = mean([air["pm2_5"][i] for i in day if air["pm2_5"][i] is not None])
        a["pm10"] = mean([air["pm10"][i] for i in day if air["pm10"][i] is not None])
        a["dust"] = "ok" if a["pm25"] <= WHO_PM25 and a["pm10"] <= WHO_PM10 else "above"
    a["hi"], a["lo"] = daily["temperature_2m_max"][-1], daily["temperature_2m_min"][-1]
    day = [i for i, t in enumerate(hourly["time"]) if t.startswith(today) and int(t[11:13]) in hours]
    feels = [col(hourly, "apparent_temperature")[i] for i in day]
    feels = [f for f in feels if f is not None] or [a["lo"], a["hi"]]  # no feels-like data -> plain temperatures
    a["feels_lo"], a["feels_hi"] = min(feels), max(feels)
    a["gusts"] = max((g for g in (col(hourly, "wind_gusts_10m")[i] for i in day) if g is not None), default=0)
    temp, rh, wind = col(hourly, "temperature_2m"), col(hourly, "relative_humidity_2m"), col(hourly, "wind_speed_10m")
    hour_of = lambda i: int(hourly["time"][i][11:13])
    a["heat"] = {hour_of(i): heat_index(temp[i], rh[i]) for i in day if temp[i] is not None and rh[i] is not None}
    a["chill"] = min((wind_chill(temp[i], wind[i] or 0) for i in day if temp[i] is not None), default=None)
    a["yesterday_hi"] = daily["temperature_2m_max"][0] if len(daily["time"]) > 1 else None
    return a


def rain_line(a):
    if a["rain"] == RAIN_SNOW:
        return f"❄️ Umbrella + good shoes — snow {hour_span(a['rain_hours'])}"
    if a["rain"] == RAIN_YES:
        return f"☔ Umbrella — rain {hour_span(a['rain_hours'])} (up to {a['top']}%)"
    if a["rain"] == RAIN_MAYBE:
        return f"🌂 Small umbrella, just in case — {a['top']}% chance {hour_span(a['rain_hours'])}"
    return ""


def sunscreen_needed(a):
    return round(a["uv"]) >= SUNSCREEN_UV


def sunscreen_line(a):
    return f"🧴 Sunscreen — UV {a['uv']:.0f} ({level(a['uv'], UV_LEVELS)}), {hour_span(a['uv_hours'])}"


def mask_needed(a):
    return a["pm25"] > MASK_PM25 or a["pm10"] > MASK_PM10


def mask_line(a):
    times = max(a["pm25"] / WHO_PM25, a["pm10"] / WHO_PM10)
    return f"😷 Mask — fine dust {times:.1f}× the WHO guideline (PM2.5 {a['pm25']:.0f} · PM10 {a['pm10']:.0f})"


def outfit_line(a):
    lo, hi = round(a["feels_lo"]), round(a["feels_hi"])
    if lo <= PADDED_BELOW:
        extra = " + windbreaker on top (windy)" if a["gusts"] >= WINDY_GUSTS else ""
        return f"🧥 Light padded jacket{extra} — feels {lo}° at the coldest"
    if lo <= WINDBREAKER_BELOW:
        warm = ", short sleeves underneath" if hi >= SHORT_SLEEVES_FROM else ""
        return f"🧥 Windbreaker{warm} — feels {lo}°–{hi}°"
    if hi >= SHORT_SLEEVES_FROM:
        return f"👕 Short sleeves — feels {lo}°–{hi}°"
    return f"👕 No jacket needed — feels {lo}°–{hi}°"


def heat_index(t_c, rh):
    """US National Weather Service heat index (°C in, °C out): simple formula, Rothfusz regression when it's hot."""
    t = t_c * 9 / 5 + 32
    hi = 0.5 * (t + 61 + (t - 68) * 1.2 + rh * 0.094)
    if (hi + t) / 2 >= 80:
        hi = (-42.379 + 2.04901523 * t + 10.14333127 * rh - 0.22475541 * t * rh - 0.00683783 * t * t
              - 0.05481717 * rh * rh + 0.00122874 * t * t * rh + 0.00085282 * t * rh * rh - 0.00000199 * t * t * rh * rh)
        if rh < 13 and 80 <= t <= 112:
            hi -= (13 - rh) / 4 * ((17 - abs(t - 95)) / 17) ** 0.5
        elif rh > 85 and 80 <= t <= 87:
            hi += (rh - 85) / 10 * (87 - t) / 5
    return (hi - 32) * 5 / 9


def wind_chill(t_c, wind_kmh):
    """2001 US/Canada wind chill (°C, km/h); only defined at 10°C or below with some wind, else the temperature."""
    if t_c > 10 or wind_kmh < 4.8:
        return t_c
    v = wind_kmh ** 0.16
    return 13.12 + 0.6215 * t_c - 11.37 * v + 0.3965 * t_c * v


def comfort_line(a):
    """One line about how the day will feel, only when it's worth saying (the most serious one wins)."""
    hot = lambda limit: [h for h, x in sorted(a["heat"].items()) if x >= limit]
    peak = round(max(a["heat"].values(), default=0))
    if hot(HEAT_DANGER):
        return f"🥵 Dangerous heat {hour_span(hot(HEAT_DANGER))} (heat index {peak}°) — stay inside, drink water"
    if hot(HEAT_EXTREME):
        return f"🥵 Heat {hour_span(hot(HEAT_EXTREME))} (heat index {peak}°) — drink water, don't stay outside long"
    if hot(HEAT_CAUTION):
        return f"💧 Hot & sticky {hour_span(hot(HEAT_CAUTION))} (heat index {peak}°) — light clothes, take breaks"
    if a["chill"] is not None and a["chill"] <= CHILL_FROSTBITE:
        return f"🥶 Frostbite risk (wind chill {round(a['chill'])}°) — cover skin, keep time outside short"
    if a["chill"] is not None and a["chill"] <= CHILL_COLD:
        return f"🥶 Very cold (wind chill {round(a['chill'])}°) — hat & gloves, don't stay outside long"
    return ""


def today_brief(place):
    """The morning message: what to bring, then what you don't need (so nothing looks forgotten)."""
    a = assess(place, DAY_HOURS)
    bring, skip = [], []
    if a["rain"]:
        bring.append(rain_line(a))
    else:
        skip.append("☔ Umbrella — no rain expected")
    bring.insert(0, outfit_line(a))
    if comfort_line(a):
        bring.insert(1, comfort_line(a))
    if sunscreen_needed(a):
        bring.append(sunscreen_line(a))
    else:
        skip.append(f"🧴 Sunscreen — UV low ({a['uv']:.0f})")
    if mask_needed(a):
        bring.append(mask_line(a))
    elif a["dust"] == "ok":
        skip.append("😷 Mask — air within WHO guideline")
    elif a["dust"]:
        times = max(a["pm25"] / WHO_PM25, a["pm10"] / WHO_PM10)
        skip.append(f"😷 Mask — air {times:.1f}× the WHO guideline (mask from {MASK_PM25 / WHO_PM25:.1f}×)")

    head = f"☀️ {datetime.now(ZoneInfo(place['tz'])):%a %m/%d} · {place['name']} · {a['hi']:.0f}° / {a['lo']:.0f}°"
    parts = [head]
    parts.append("Bring:\n" + "\n".join(bring) if bring else "✅ Nothing extra to bring today")
    if skip:
        parts.append("Not needed:\n" + "\n".join(skip))
    seen = {"rain": a["rain"], "mask": mask_needed(a), "uv": sunscreen_needed(a)}
    return "\n\n".join(parts), seen


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
        # The repo (and its Actions logs) is public: never log chat ids, message text or places.
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
        if not STATE_KEY:  # the repo is public: never save a location unencrypted
            send("🔒 Add the STATE_KEY secret first (Settings -> Secrets and variables -> Actions), "
                 "then send /location again. Your location is only saved encrypted.")
            return
        found = find_place(arg)
        if not found:
            send(f"❔ Couldn't find \"{arg}\". Try the English name or add the country, e.g. /location Portland, US")
            return
        state["place"] = found
        state.pop("last_sent", None)
        state.pop("today", None)
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
        send(today_brief(place)[0])

    elif cmd == "/settings":
        where = place_label(place) if place else "not set — /location Seoul"
        send(f"⚙️ Settings\n📍 Location: {where}\n⏰ Daily message: {state.get('time', DEFAULT_TIME)}\n"
             f"🔔 Updates if the weather gets worse: until {UPDATE_UNTIL_HOUR}:00")

    else:
        intro = "" if place else "👋 First, set your location: /location Seoul\n\n"
        send(intro + HELP)


# ---------- Daily message + updates ----------
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
        text, seen = today_brief(place)
        send(text)
        state["today"] = {"date": today, "checked": now.hour, **seen}
    state["last_sent"] = today  # also marks a skipped (too late) day, so it isn't retried every run


def check_updates(state):
    """After the morning message, re-check hourly and message only if something new is needed (rain, sun, dust)."""
    place, seen = state.get("place"), state.get("today")
    if not place or not seen:
        return
    now = datetime.now(ZoneInfo(place["tz"]))
    if seen["date"] != now.date().isoformat() or now.hour >= UPDATE_UNTIL_HOUR or seen.get("checked") == now.hour:
        return
    seen["checked"] = now.hour
    a = assess(place, range(now.hour, 24))  # only what's still ahead today
    news = []
    if a["rain"] >= RAIN_YES and a["rain"] > seen["rain"]:
        news.append(rain_line(a))
    if sunscreen_needed(a) and not seen.get("uv"):
        news.append(sunscreen_line(a))
    if mask_needed(a) and not seen["mask"]:
        news.append(mask_line(a))
    if news:
        send(f"⚠️ Weather changed · {place['name']}\n\nBring now:\n" + "\n".join(news))
        seen["rain"] = max(seen["rain"], a["rain"])
        seen["uv"] = seen.get("uv") or sunscreen_needed(a)
        seen["mask"] = seen["mask"] or mask_needed(a)


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
    if not TOKEN or not CHAT_ID:  # clearer than Telegram's bare 404 when the secrets aren't added yet
        raise SystemExit("TG_TOKEN or TG_CHAT_ID secret is missing: add them in Settings -> Secrets and variables -> Actions")
    state = load_state()
    handle_commands(state)
    try:
        send_daily(state)
    except Exception as e:  # weather service down -> try again next run (last_sent isn't set)
        print(f"daily message failed: {why(e)}")
    try:
        check_updates(state)
    except Exception as e:  # try again next hour
        print(f"update check failed: {why(e)}")
    # guarantees a commit at least monthly, so GitHub doesn't disable the schedule after 60 idle days
    state["heartbeat"] = time.strftime("%Y-%m")
    save_state(state)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # the default traceback could print a place or URL in the public log
        raise SystemExit(f"run failed: {why(e)}")
