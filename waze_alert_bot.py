"""
Waze Partner Feed — Live Webpage Updater & 30-Minute Batched Telegram Bot

Designed for scheduled GitHub Actions (`--once` every 5 minutes) as well as
continuous local/cloud execution:
1. Fetches the Waze Partner Feed every 5 minutes (10s timeout, zero pip deps).
2. Normalizes live alerts, traffic jams, road closures, and irregularities into
   `alerts.json` and `alerts_data.js` for the GitHub Pages live map.
3. Tracks alert persistence across 5-minute pings in `data/bot_state.json`.
4. Dispatches Telegram notifications in batches every 30 minutes (6 scheduled
   fetches) ONLY for alerts that:
   - Still exist in the latest fetch,
   - Have NOT expired in the last 2 ping intervals (present in both of the
     most recent 2 fetches),
   - Occurred at least 2 times within the 30-minute window, and
   - Have not already been sent in a previous Telegram batch.
"""

import html
import json
import os
import random
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

# Indian Standard Time (IST = UTC + 5:30)
IST = timezone(timedelta(hours=5, minutes=30))

BASE_DIR = Path(__file__).resolve().parent
ALERTS_JSON_PATH = BASE_DIR / "alerts.json"
ALERTS_JS_PATH = BASE_DIR / "alerts_data.js"
STATE_FILE_PATH = BASE_DIR / "data" / "bot_state.json"


def load_env(env_path: Path = BASE_DIR / ".env") -> None:
    """Load KEY=VALUE pairs from .env if not already set (or empty) in os.environ."""
    if not env_path.exists():
        return
    try:
        with open(env_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                k = k.strip()
                v = v.strip().strip("'\"")
                if k and not os.environ.get(k):
                    os.environ[k] = v
    except Exception as e:
        print(f"[WARN] Could not parse .env: {e}", file=sys.stderr)


load_env()

WAZE_FEED_URL = (os.getenv("WAZE_FEED_URL") or "").strip()
WAZE_ROW_FEED_URL = (os.getenv("WAZE_ROW_FEED_URL") or "").strip()
TELEGRAM_BOT_TOKEN = (os.getenv("TELEGRAM_BOT_TOKEN") or "").strip()
TELEGRAM_CHAT_ID = (os.getenv("TELEGRAM_CHAT_ID") or "").strip()

POLL_INTERVAL_SECONDS = int(os.getenv("POLL_INTERVAL") or "300")
BATCH_WINDOW_MINUTES = int(os.getenv("BATCH_WINDOW_MINUTES") or "30")
BATCH_TARGET_PINGS = int(os.getenv("BATCH_TARGET_PINGS") or "6")
MIN_OCCURRENCES_IN_WINDOW = int(os.getenv("MIN_OCCURRENCES_IN_WINDOW") or "2")
TELEGRAM_ALERT_TYPES_RAW = (os.getenv("TELEGRAM_ALERT_TYPES") or "ALL").strip().upper()
INDIA_ONLY_STRICT = (os.getenv("INDIA_ONLY") or "false").strip().lower() == "true"

# India Geographic Bounding Box (Lat 6°N–38°N, Lon 68°E–98°E)
INDIA_LAT_MIN, INDIA_LAT_MAX = 6.0, 38.0
INDIA_LON_MIN, INDIA_LON_MAX = 68.0, 98.0

CATEGORY_PRIORITY = {
    "ROAD_CLOSED": 0,
    "ACCIDENT": 1,
    "HAZARD": 2,
    "JAM": 3,
    "POLICE": 4,
}

CATEGORY_META = {
    "ROAD_CLOSED": {"icon": "⛔", "label": "Road Closure"},
    "ACCIDENT": {"icon": "💥", "label": "Accident"},
    "HAZARD": {"icon": "⚠️", "label": "Hazard"},
    "JAM": {"icon": "🚗", "label": "Heavy Traffic"},
    "POLICE": {"icon": "👮", "label": "Police"},
}

JAM_LEVEL_NAMES = {
    1: "Light Traffic",
    2: "Moderate Traffic",
    3: "Heavy Traffic",
    4: "Standstill Traffic",
    5: "Road Blocked",
}

NOTIFIED_TTL_SECONDS = 48 * 3600  # Prune old notified UUIDs after 48h of absence


def format_ist(epoch_ms: int | float | None) -> str:
    if not epoch_ms:
        return "Recent"
    dt = datetime.fromtimestamp(float(epoch_ms) / 1000.0, tz=timezone.utc).astimezone(IST)
    return dt.strftime("%d %b %Y, %I:%M %p IST")


def is_in_india_coords(lat: float | None, lon: float | None, country: str = "") -> bool:
    if (country or "").strip().upper() == "IN":
        return True
    if lat is not None and lon is not None:
        return INDIA_LAT_MIN <= lat <= INDIA_LAT_MAX and INDIA_LON_MIN <= lon <= INDIA_LON_MAX
    return False


def build_waze_live_map_url(lat: float, lon: float) -> str:
    return f"https://www.waze.com/live-map/directions?to=ll.{lat:.6f}%2C{lon:.6f}"


def build_waze_app_url(lat: float, lon: float) -> str:
    return f"https://waze.com/ul?ll={lat:.6f},{lon:.6f}&navigate=yes"


def pretty_subtype(subtype: str | None, alert_type: str | None) -> str:
    raw = (subtype or "").strip()
    if not raw:
        return ""
    prefix = (alert_type or "").strip() + "_"
    if prefix != "_" and raw.startswith(prefix):
        raw = raw[len(prefix):]
    return raw.replace("_", " ").strip().title()


def to_latlng_list(points: list | None) -> list[list[float]]:
    coords: list[list[float]] = []
    for p in points or []:
        if isinstance(p, dict) and "x" in p and "y" in p:
            try:
                coords.append([round(float(p["y"]), 6), round(float(p["x"]), 6)])
            except (TypeError, ValueError):
                continue
    return coords


def extract_alert_latlon(alert: dict) -> tuple[float | None, float | None]:
    loc = alert.get("location")
    if isinstance(loc, dict) and "x" in loc and "y" in loc:
        try:
            return round(float(loc["y"]), 6), round(float(loc["x"]), 6)
        except (TypeError, ValueError):
            pass
    pos = alert.get("position")
    if isinstance(pos, str) and " " in pos.strip():
        parts = pos.strip().split()
        try:
            return round(float(parts[0]), 6), round(float(parts[1]), 6)
        except (TypeError, ValueError):
            pass
    return None, None


def classify_waze_alert(alert: dict) -> tuple[str | None, str, int]:
    """Map raw Waze alert type/subtype into UI category, severity, and jamLevel."""
    t = (alert.get("type") or "").strip().upper()
    st = (alert.get("subtype") or "").strip().upper()

    if t == "CHIT_CHAT":
        return None, "", 0
    if t == "ROAD_CLOSED":
        return "ROAD_CLOSED", "closed", 5
    if t == "ACCIDENT":
        sev = "critical" if st == "ACCIDENT_MAJOR" else "heavy"
        return "ACCIDENT", sev, 4
    if t == "POLICE":
        return "POLICE", "moderate", 2
    if t == "JAM":
        lvl = {
            "JAM_LIGHT_TRAFFIC": 1,
            "JAM_MODERATE_TRAFFIC": 2,
            "JAM_HEAVY_TRAFFIC": 3,
            "JAM_STAND_STILL_TRAFFIC": 4,
        }.get(st, 3)
        sev = {1: "low", 2: "moderate", 3: "heavy", 4: "critical"}[lvl]
        return "JAM", sev, lvl
    # HAZARD, WEATHERHAZARD, CONSTRUCTION, or other valid road events
    return "HAZARD", "heavy", 3


def fetch_single_feed(feed_url: str) -> dict:
    """Fetch a single Waze Partner Feed JSON document with a 10s hard timeout."""
    req = urllib.request.Request(
        feed_url,
        headers={
            "User-Agent": "Mozilla/5.0 (compatible; WazeIndiaAlertsBot/2.0)",
            "Accept": "application/json",
        },
    )
    with urllib.request.urlopen(req, timeout=10) as resp:
        return json.loads(resp.read().decode("utf-8"))


def fetch_combined_feeds() -> dict:
    """
    Fetch primary WAZE_FEED_URL and optional WAZE_ROW_FEED_URL, deduplicating
    collections by uuid/id. Raises if all configured URLs fail.
    """
    urls: list[str] = []
    for candidate in (WAZE_ROW_FEED_URL, WAZE_FEED_URL):
        if candidate and candidate not in urls:
            urls.append(candidate)

    if not urls:
        raise RuntimeError("No WAZE_FEED_URL configured in environment or .env")

    merged_alerts: dict[str, dict] = {}
    merged_jams: dict[str, dict] = {}
    merged_irrs: dict[str, dict] = {}
    end_time_millis: int | None = None
    any_success = False
    last_error: Exception | None = None

    for url in urls:
        try:
            data = fetch_single_feed(url)
            any_success = True
            if data.get("endTimeMillis"):
                end_time_millis = max(end_time_millis or 0, int(data["endTimeMillis"]))
            for a in data.get("alerts") or []:
                uid = str(a.get("uuid") or "").strip()
                if uid:
                    merged_alerts[uid] = a
            for j in data.get("jams") or []:
                uid = str(j.get("uuid") or j.get("id") or "").strip()
                if uid:
                    merged_jams[uid] = j
            for irr in data.get("irregularities") or []:
                uid = str(irr.get("id") or irr.get("uuid") or "").strip()
                if uid:
                    merged_irrs[uid] = irr
        except Exception as e:
            last_error = e
            print(f"[WARN] Feed request failed ({url[:48]}...): {e}", file=sys.stderr)

    if not any_success:
        raise last_error or RuntimeError("All Waze feed requests failed")

    return {
        "endTimeMillis": end_time_millis or int(time.time() * 1000),
        "alerts": list(merged_alerts.values()),
        "jams": list(merged_jams.values()),
        "irregularities": list(merged_irrs.values()),
    }


def normalize_feed(feed: dict, occurrence_lookup: dict[str, int] | None = None) -> dict:
    """
    Normalize raw Waze Partner Feed JSON into a flat, sorted event payload
    ready for `alerts.json` and Telegram batching.
    """
    occurrence_lookup = occurrence_lookup or {}
    alerts = feed.get("alerts") or []
    jams = feed.get("jams") or []
    irrs = feed.get("irregularities") or []

    events: list[dict] = []
    closure_alerts_by_uuid: dict[str, dict] = {}

    # 1. Process User/Partner Alerts
    for a in alerts:
        uid = str(a.get("uuid") or "").strip()
        if not uid:
            continue
        category, severity, jam_level = classify_waze_alert(a)
        if not category:
            continue
        lat, lon = extract_alert_latlon(a)
        if lat is None or lon is None:
            continue

        country = (a.get("country") or "").strip().upper()
        in_india = is_in_india_coords(lat, lon, country)
        street = (a.get("street") or "").strip() or "Unnamed Road"
        city = (a.get("city") or "").strip() or ("India" if in_india else (country or "Partner Area"))
        sub_label = pretty_subtype(a.get("subtype"), a.get("type"))
        raw_desc = (a.get("reportDescription") or "").strip()

        desc_parts = [p for p in (sub_label, raw_desc) if p]
        desc = " — ".join(desc_parts) if desc_parts else f"Active {CATEGORY_META[category]['label'].lower()} reported on Waze."

        ev = {
            "id": f"alert_{uid}",
            "uuid": uid,
            "entityKind": "alert",
            "type": category,
            "rawType": (a.get("type") or "").strip(),
            "subtype": (a.get("subtype") or "").strip(),
            "subtypeLabel": sub_label or CATEGORY_META[category]["label"],
            "severity": severity,
            "jamLevel": jam_level,
            "street": street,
            "city": city,
            "country": country,
            "inIndia": in_india,
            "desc": desc,
            "reportDescription": raw_desc,
            "lat": lat,
            "lon": lon,
            "coordinates": [],
            "lengthMeters": 0,
            "delaySeconds": 0,
            "speedKmh": None,
            "pubMillis": int(a["pubMillis"]) if a.get("pubMillis") else None,
            "thumbsUp": int(a.get("nThumbsUp") or 0),
            "reliability": int(a.get("reliability") or 0),
            "reportRating": int(a.get("reportRating") or 0),
            "occurrenceCount": occurrence_lookup.get(uid, 1),
        }
        events.append(ev)
        if category == "ROAD_CLOSED":
            closure_alerts_by_uuid[uid] = ev

    # 2. Process Traffic Jams & Blocked Segments
    for j in jams:
        j_uid = str(j.get("uuid") or j.get("id") or "").strip()
        if not j_uid:
            continue
        lvl = int(j.get("level") or 0)
        raw_delay = int(j.get("delay") or 0)
        delay = max(0, raw_delay)
        blocking_uuid = str(j.get("blockingAlertUuid") or "").strip()
        closed = (lvl == 5) or (raw_delay == -1) or bool(blocking_uuid)
        coords = to_latlng_list(j.get("line"))

        # Link jam geometry to its causing ROAD_CLOSED alert instead of duplicating
        if blocking_uuid and blocking_uuid in closure_alerts_by_uuid:
            cause = closure_alerts_by_uuid[blocking_uuid]
            if not cause["coordinates"] and coords:
                cause["coordinates"] = coords
            if not cause["lengthMeters"]:
                cause["lengthMeters"] = int(j.get("length") or 0)
            cause["linkedJamId"] = f"jam_{j_uid}"
            continue

        if not coords:
            continue

        mid = coords[len(coords) // 2]
        lat, lon = mid[0], mid[1]
        country = (j.get("country") or "").strip().upper()
        in_india = is_in_india_coords(lat, lon, country)
        street = (j.get("street") or "").strip() or "Unnamed Corridor"
        city = (j.get("city") or "").strip() or ("India" if in_india else (country or "Partner Area"))
        length_m = int(j.get("length") or 0)
        speed_kmh = round(float(j.get("speedKMH") or 0.0), 1)

        category = "ROAD_CLOSED" if closed else "JAM"
        eff_level = 5 if closed else max(1, min(lvl, 4))
        if closed:
            desc = f"Road segment blocked ({length_m} m)."
            sub_label = "Blocked Segment"
        else:
            delay_min = max(1, round(delay / 60)) if delay >= 30 else 0
            delay_txt = f"+{delay_min} min delay" if delay_min else f"{delay}s delay"
            desc = f"{JAM_LEVEL_NAMES.get(eff_level, 'Traffic Jam')} • {length_m} m • Avg {speed_kmh} km/h ({delay_txt})."
            sub_label = JAM_LEVEL_NAMES.get(eff_level, "Traffic Jam")

        jam_key = f"jam_{j_uid}"
        events.append({
            "id": jam_key,
            "uuid": jam_key,
            "entityKind": "jam",
            "type": category,
            "rawType": "JAM",
            "subtype": f"JAM_LEVEL_{eff_level}",
            "subtypeLabel": sub_label,
            "severity": "closed" if closed else {1: "low", 2: "moderate", 3: "heavy", 4: "critical"}[eff_level],
            "jamLevel": eff_level,
            "street": street,
            "city": city,
            "country": country,
            "inIndia": in_india,
            "desc": desc,
            "reportDescription": "",
            "lat": lat,
            "lon": lon,
            "coordinates": coords,
            "lengthMeters": length_m,
            "delaySeconds": delay,
            "speedKmh": speed_kmh,
            "pubMillis": int(j["pubMillis"]) if j.get("pubMillis") else None,
            "thumbsUp": 0,
            "reliability": 10,
            "reportRating": 5,
            "occurrenceCount": occurrence_lookup.get(jam_key, 1),
        })

    # 3. Process Irregularities
    for irr in irrs:
        i_uid = str(irr.get("id") or irr.get("uuid") or "").strip()
        coords = to_latlng_list(irr.get("line"))
        if not i_uid or not coords:
            continue
        mid = coords[len(coords) // 2]
        lat, lon = mid[0], mid[1]
        country = (irr.get("country") or "").strip().upper()
        in_india = is_in_india_coords(lat, lon, country)
        street = (irr.get("street") or "").strip() or "Unnamed Corridor"
        city = (irr.get("city") or "").strip() or ("India" if in_india else (country or "Partner Area"))
        lvl = max(1, min(int(irr.get("jamLevel") or 3), 5))
        delay = max(0, int(irr.get("delaySeconds") or irr.get("seconds") or 0))
        length_m = int(irr.get("length") or 0)
        speed_kmh = round(float(irr.get("speed") or 0.0), 1)
        reg_speed = round(float(irr.get("regularSpeed") or 0.0), 1)
        irr_key = f"irr_{i_uid}"

        events.append({
            "id": irr_key,
            "uuid": irr_key,
            "entityKind": "irregularity",
            "type": "JAM",
            "rawType": "IRREGULARITY",
            "subtype": "IRREGULARITY",
            "subtypeLabel": "Unusual Congestion",
            "severity": "critical" if lvl >= 4 else "heavy",
            "jamLevel": lvl,
            "street": street,
            "city": city,
            "country": country,
            "inIndia": in_india,
            "desc": f"Unusual traffic ({length_m} m) • {speed_kmh} km/h vs normal {reg_speed} km/h (+{delay // 60} min).",
            "reportDescription": "",
            "lat": lat,
            "lon": lon,
            "coordinates": coords,
            "lengthMeters": length_m,
            "delaySeconds": delay,
            "speedKmh": speed_kmh,
            "pubMillis": int(irr.get("updateDateMillis") or irr.get("detectionDateMillis") or 0) or None,
            "thumbsUp": int(irr.get("nThumbsUp") or 0),
            "reliability": 10,
            "reportRating": 5,
            "occurrenceCount": occurrence_lookup.get(irr_key, 1),
        })

    # Region selection:
    # - If INDIA_ONLY=true, keep only India events.
    # - Otherwise, if India events exist alongside demo IL events, prefer India events;
    #   if no India events exist yet (e.g. using the IL partner feed from .env), keep all
    #   partner polygon events so live updates still populate the webpage and Telegram.
    india_events = [e for e in events if e["inIndia"]]
    if INDIA_ONLY_STRICT:
        events = india_events
    elif india_events:
        events = india_events

    # Sort: closures -> accidents -> hazards -> jams -> police, then severity/delay/recency
    events.sort(
        key=lambda e: (
            CATEGORY_PRIORITY.get(e["type"], 9),
            -int(e.get("jamLevel") or 0),
            -int(e.get("delaySeconds") or 0),
            -int(e.get("pubMillis") or 0),
        )
    )

    counts = {"ALL": len(events)}
    for cat in CATEGORY_PRIORITY:
        counts[cat] = sum(1 for e in events if e["type"] == cat)

    # Cities sorted by highest active report count
    city_counts: dict[str, int] = {}
    for e in events:
        c = e.get("city") or ""
        if c:
            city_counts[c] = city_counts.get(c, 0) + 1
    cities = [c for c, _ in sorted(city_counts.items(), key=lambda kv: (-kv[1], kv[0]))]

    # Bounding box [minLat, minLon, maxLat, maxLon]
    bbox = None
    if events:
        lats = [e["lat"] for e in events if e.get("lat") is not None]
        lons = [e["lon"] for e in events if e.get("lon") is not None]
        if lats and lons:
            bbox = [min(lats), min(lons), max(lats), max(lons)]

    now_ms = int(time.time() * 1000)
    return {
        "updatedAtMillis": now_ms,
        "updatedAtIST": format_ist(now_ms),
        "feedEndTimeMillis": feed.get("endTimeMillis"),
        "isStale": False,
        "lastGoodAtMillis": now_ms,
        "lastGoodAtIST": format_ist(now_ms),
        "counts": counts,
        "cities": cities,
        "bbox": bbox,
        "events": events,
    }


def is_telegram_candidate(event: dict) -> bool:
    """
    Determine whether a normalized event should be tracked for Telegram batch alerts.
    Tracks all Waze user/partner alerts plus standalone road-closure segments.
    """
    if event.get("entityKind") == "jam" and event.get("type") != "ROAD_CLOSED":
        return False
    if event.get("entityKind") == "irregularity":
        return False

    if TELEGRAM_ALERT_TYPES_RAW and TELEGRAM_ALERT_TYPES_RAW != "ALL":
        allowed = {x.strip() for x in TELEGRAM_ALERT_TYPES_RAW.split(",") if x.strip()}
        return event.get("type") in allowed
    return True


def load_state() -> dict:
    if STATE_FILE_PATH.exists():
        try:
            with open(STATE_FILE_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, dict):
                    return data
        except Exception as e:
            print(f"[WARN] Could not read state file {STATE_FILE_PATH}: {e}", file=sys.stderr)
    return {
        "window_started_at": 0,
        "last_batch_sent_at": 0,
        "total_fetches": 0,
        "window_pings": [],
        "recent_pings": [],
        "alert_records": {},
        "notified_uuids": {},
    }


def save_state(state: dict) -> None:
    STATE_FILE_PATH.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = STATE_FILE_PATH.with_suffix(".tmp")
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)
    tmp_path.replace(STATE_FILE_PATH)


def write_webpage_payload(payload: dict) -> None:
    """Write normalized live events to both `alerts.json` and `alerts_data.js`."""
    json_text = json.dumps(payload, ensure_ascii=False, indent=2)
    ALERTS_JSON_PATH.write_text(json_text, encoding="utf-8")
    ALERTS_JS_PATH.write_text(
        f"window.__WAZE_LIVE_DATA__ = {json_text};\n",
        encoding="utf-8",
    )


def mark_existing_payload_stale() -> None:
    """Keep the last good payload on outage and flag `isStale: true`."""
    if not ALERTS_JSON_PATH.exists():
        return
    try:
        payload = json.loads(ALERTS_JSON_PATH.read_text(encoding="utf-8"))
        now_ms = int(time.time() * 1000)
        payload["isStale"] = True
        payload["lastCheckedAtMillis"] = now_ms
        payload["lastCheckedAtIST"] = format_ist(now_ms)
        write_webpage_payload(payload)
    except Exception as e:
        print(f"[WARN] Could not mark existing alerts.json stale: {e}", file=sys.stderr)


def format_batch_messages(
    qualified_alerts: list[dict],
    ping_counts: dict[str, int],
    total_pings_in_window: int,
    window_start_sec: int,
    now_sec: int,
) -> list[str]:
    """
    Build HTML-formatted Telegram batch message(s), splitting cleanly into pages
    if a batch has more than 10 alerts so we never exceed Telegram's 4096-char limit.
    """
    start_str = datetime.fromtimestamp(window_start_sec, tz=timezone.utc).astimezone(IST).strftime("%I:%M %p")
    end_str = datetime.fromtimestamp(now_sec, tz=timezone.utc).astimezone(IST).strftime("%d %b %Y, %I:%M %p IST")

    page_size = 10
    total_pages = max(1, (len(qualified_alerts) + page_size - 1) // page_size)
    messages: list[str] = []

    for page_idx in range(total_pages):
        chunk = qualified_alerts[page_idx * page_size : (page_idx + 1) * page_size]
        page_suffix = f" ({page_idx + 1}/{total_pages})" if total_pages > 1 else ""

        lines = [
            f"🚨 <b>Waze Live Alerts — 30-Min Verified Batch{page_suffix}</b>",
            f"🕒 <b>Window:</b> {start_str} – {end_str} ({total_pings_in_window} fetches)",
            f"✅ <b>Persistent Alerts:</b> {len(qualified_alerts)} <i>(active ≥{MIN_OCCURRENCES_IN_WINDOW} pings &amp; unexpired in last 2 intervals)</i>",
            "",
        ]

        for idx, ev in enumerate(chunk, start=page_idx * page_size + 1):
            meta = CATEGORY_META.get(ev["type"], {"icon": "⚠️", "label": ev["type"]})
            street = html.escape(ev.get("street") or "Unnamed Road")
            city = html.escape(ev.get("city") or "Unknown City")
            country = html.escape(ev.get("country") or "")
            sub = html.escape(ev.get("subtypeLabel") or meta["label"])
            note = html.escape(ev.get("reportDescription") or "")
            lat = float(ev.get("lat") or 0.0)
            lon = float(ev.get("lon") or 0.0)
            seen_n = ping_counts.get(ev["uuid"], MIN_OCCURRENCES_IN_WINDOW)
            rep_time = html.escape(format_ist(ev.get("pubMillis")))

            live_url = html.escape(build_waze_live_map_url(lat, lon), quote=True)
            app_url = html.escape(build_waze_app_url(lat, lon), quote=True)
            city_disp = f"{city} ({country})" if country and country != "IN" and country not in city else city

            lines.append(f"{idx}. {meta['icon']} <b>{sub} — {street}</b>")
            lines.append(f"   🏙 {city_disp} • 🔁 {seen_n}/{total_pings_in_window} pings • 🕒 {rep_time}")
            if note:
                lines.append(f"   📝 {note}")
            lines.append(f'   📍 <a href="{live_url}">Waze Live Map</a> | <a href="{app_url}">Open in App</a>')
            lines.append("")

        messages.append("\n".join(lines).strip())

    return messages


def send_telegram_batch(
    token: str,
    chat_id: str,
    qualified_alerts: list[dict],
    ping_counts: dict[str, int],
    total_pings_in_window: int,
    window_start_sec: int,
    now_sec: int,
) -> bool:
    """Send 30-minute verified alert batch to Telegram."""
    messages = format_batch_messages(
        qualified_alerts,
        ping_counts,
        total_pings_in_window,
        window_start_sec,
        now_sec,
    )

    if not token or not chat_id:
        print("\n" + "=" * 60)
        print("[DRY RUN] Telegram credentials missing. Simulated 30-min batch:")
        for m in messages:
            print(m)
            print("-" * 60)
        return True

    telegram_url = f"https://api.telegram.org/bot{token}/sendMessage"
    all_ok = True

    for m in messages:
        payload = {
            "chat_id": chat_id,
            "text": m,
            "parse_mode": "HTML",
            "disable_web_page_preview": True,
        }
        try:
            req = urllib.request.Request(
                telegram_url,
                data=json.dumps(payload).encode("utf-8"),
                headers={
                    "Content-Type": "application/json",
                    "User-Agent": "WazeIndiaAlertsBot/2.0",
                },
            )
            with urllib.request.urlopen(req, timeout=15) as resp:
                if resp.status != 200:
                    all_ok = False
        except urllib.error.HTTPError as e:
            err_body = ""
            try:
                err_body = e.read().decode("utf-8", errors="replace")
            except Exception:
                pass
            print(f"[ERROR] Telegram HTTP {e.code}: {err_body or e.reason}", file=sys.stderr)
            all_ok = False
        except Exception as e:
            print(f"[ERROR] Failed to send Telegram batch: {e}", file=sys.stderr)
            all_ok = False

    if all_ok:
        print(f"[TELEGRAM] Sent 30-minute batch with {len(qualified_alerts)} verified alert(s) ({len(messages)} message(s)).")
    return all_ok


# --- Mock Mode Generator for Local Verification ---
MOCK_POOL = [
    {
        "uuid": "mock-blr-orr-closure",
        "type": "ROAD_CLOSED",
        "subtype": "ROAD_CLOSED_CONSTRUCTION",
        "street": "Outer Ring Road (Bellandur Flyover)",
        "city": "Bengaluru",
        "country": "IN",
        "location": {"x": 77.6744, "y": 12.9299},
        "reportDescription": "Metro flyover girder launching — use service lane",
        "nThumbsUp": 24,
        "reliability": 9,
        "reportRating": 5,
    },
    {
        "uuid": "mock-mum-weh-closure",
        "type": "ROAD_CLOSED",
        "subtype": "ROAD_CLOSED_HAZARD",
        "street": "Western Express Highway (Bandra Kalanagar)",
        "city": "Mumbai",
        "country": "IN",
        "location": {"x": 72.8295, "y": 19.0596},
        "reportDescription": "Emergency expansion joint repair work",
        "nThumbsUp": 31,
        "reliability": 10,
        "reportRating": 5,
    },
    {
        "uuid": "mock-del-nh48-accident",
        "type": "ACCIDENT",
        "subtype": "ACCIDENT_MAJOR",
        "street": "Delhi-Gurgaon Expressway (NH-48)",
        "city": "Delhi NCR",
        "country": "IN",
        "location": {"x": 77.0895, "y": 28.4950},
        "reportDescription": "Two right lanes blocked near Cyber City exit",
        "nThumbsUp": 18,
        "reliability": 8,
        "reportRating": 4,
    },
    {
        "uuid": "mock-transient-hazard",
        "type": "HAZARD",
        "subtype": "HAZARD_ON_ROAD_POT_HOLE",
        "street": "Anna Salai (Mount Road)",
        "city": "Chennai",
        "country": "IN",
        "location": {"x": 80.2458, "y": 13.0425},
        "reportDescription": "Deep pothole in center lane",
        "nThumbsUp": 9,
        "reliability": 7,
        "reportRating": 4,
    },
]


def build_mock_feed(fetch_index: int) -> dict:
    now_ms = int(time.time() * 1000)
    alerts = []
    # First 3 mock alerts stay persistent; 4th appears only sporadically
    for item in MOCK_POOL[:3]:
        alerts.append({**item, "pubMillis": now_ms - 600_000})
    if fetch_index % 3 == 1:
        alerts.append({**MOCK_POOL[3], "uuid": f"mock-ephemeral-{fetch_index}", "pubMillis": now_ms})
    return {"endTimeMillis": now_ms, "alerts": alerts, "jams": [], "irregularities": []}


def qualify_alerts_for_batch(
    window_pings: list[dict],
    alert_records: dict[str, dict],
    notified_uuids: dict[str, int],
    min_occurrences: int = MIN_OCCURRENCES_IN_WINDOW,
) -> tuple[list[dict], dict[str, int]]:
    """
    Evaluate which alerts qualify for the 30-minute Telegram batch:
    1. Must still exist right now (in `window_pings[-1]`).
    2. Must NOT have expired in the last 2 ping intervals (in both `window_pings[-2]` and `window_pings[-1]`).
    3. Must have occurred at least `min_occurrences` (>= 2) times in `window_pings`.
    4. Must not already be in `notified_uuids`.
    """
    if len(window_pings) < 2:
        return [], {}

    latest_uuids = set(window_pings[-1].get("uuids") or [])
    prev_uuids = set(window_pings[-2].get("uuids") or [])
    unexpired_last_two = latest_uuids & prev_uuids

    ping_counts: dict[str, int] = {}
    for u in unexpired_last_two:
        ping_counts[u] = sum(1 for p in window_pings if u in (p.get("uuids") or []))

    qualified: list[dict] = []
    for u in unexpired_last_two:
        if ping_counts[u] < min_occurrences:
            continue
        if u in notified_uuids:
            continue
        rec = alert_records.get(u)
        if rec:
            qualified.append(rec)

    qualified.sort(
        key=lambda e: (
            CATEGORY_PRIORITY.get(e.get("type", ""), 9),
            -ping_counts.get(e["uuid"], 0),
            -int(e.get("pubMillis") or 0),
        )
    )
    return qualified, ping_counts


def run_cycle(use_mock: bool = False, force_batch: bool = False) -> bool:
    """Execute one 5-minute fetch, update webpage JSON, and evaluate 30-min Telegram batch."""
    state = load_state()
    now_sec = int(time.time())
    next_fetch_num = int(state.get("total_fetches") or 0) + 1

    try:
        if use_mock:
            raw_feed = build_mock_feed(next_fetch_num)
        else:
            raw_feed = fetch_combined_feeds()
    except Exception as e:
        print(f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] [FETCH ERROR] {e}", file=sys.stderr)
        mark_existing_payload_stale()
        return False

    # Build rolling occurrence map including this fetch's preliminary normalize pass
    prelim = normalize_feed(raw_feed)
    candidate_events = [e for e in prelim["events"] if is_telegram_candidate(e)]
    current_candidate_uuids = sorted({e["uuid"] for e in candidate_events})

    # Update ping windows
    window_pings: list[dict] = list(state.get("window_pings") or [])
    recent_pings: list[dict] = list(state.get("recent_pings") or [])
    window_started_at = int(state.get("window_started_at") or 0)
    if window_started_at <= 0:
        # Align window start 1 poll interval before the first ping so 6 pings = 30 mins
        window_started_at = now_sec - POLL_INTERVAL_SECONDS

    ping_entry = {"timestamp": now_sec, "uuids": current_candidate_uuids}
    window_pings.append(ping_entry)
    recent_pings = (recent_pings + [ping_entry])[-max(BATCH_TARGET_PINGS, 6) :]

    # Count occurrences across recent 30-min rolling window for UI display
    all_event_uuids = {e["uuid"] for e in prelim["events"]}
    occurrence_lookup: dict[str, int] = {}
    for uid in all_event_uuids:
        c = sum(1 for p in recent_pings if uid in (p.get("uuids") or []))
        occurrence_lookup[uid] = max(1, c)

    # Finalize normalized webpage payload with occurrence counts & batch progress
    payload = normalize_feed(raw_feed, occurrence_lookup=occurrence_lookup)
    payload["pingCountInWindow"] = len(window_pings)
    payload["batchTargetPings"] = BATCH_TARGET_PINGS
    payload["batchWindowMinutes"] = BATCH_WINDOW_MINUTES
    write_webpage_payload(payload)

    # Update stored candidate alert snapshots & prune stale records
    alert_records: dict[str, dict] = dict(state.get("alert_records") or {})
    for ev in payload["events"]:
        if is_telegram_candidate(ev):
            alert_records[ev["uuid"]] = {**ev, "last_seen_at": now_sec}

    alert_records = {
        uid: rec
        for uid, rec in alert_records.items()
        if now_sec - int(rec.get("last_seen_at") or now_sec) <= NOTIFIED_TTL_SECONDS
    }

    notified_uuids: dict[str, int] = {
        uid: int(ts)
        for uid, ts in (state.get("notified_uuids") or {}).items()
        if uid in alert_records or (now_sec - int(ts) <= NOTIFIED_TTL_SECONDS)
    }

    elapsed_sec = now_sec - window_started_at
    is_batch_due = (
        len(window_pings) >= BATCH_TARGET_PINGS
        or (len(window_pings) >= 2 and elapsed_sec >= (BATCH_WINDOW_MINUTES * 60 - 60))
        or (force_batch and len(window_pings) >= 2)
    )

    print(
        f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] Fetch #{next_fetch_num} complete: "
        f"{payload['counts']['ALL']} live map event(s), "
        f"{len(current_candidate_uuids)} candidate alert(s) "
        f"(window ping {len(window_pings)}/{BATCH_TARGET_PINGS}, elapsed {elapsed_sec // 60}m)."
    )

    if is_batch_due:
        qualified, ping_counts = qualify_alerts_for_batch(
            window_pings=window_pings,
            alert_records=alert_records,
            notified_uuids=notified_uuids,
            min_occurrences=MIN_OCCURRENCES_IN_WINDOW,
        )
        if qualified:
            sent = send_telegram_batch(
                token=TELEGRAM_BOT_TOKEN,
                chat_id=TELEGRAM_CHAT_ID,
                qualified_alerts=qualified,
                ping_counts=ping_counts,
                total_pings_in_window=len(window_pings),
                window_start_sec=window_started_at,
                now_sec=now_sec,
            )
            if sent:
                for ev in qualified:
                    notified_uuids[ev["uuid"]] = now_sec
                state["last_batch_sent_at"] = now_sec
                window_pings = []
                window_started_at = now_sec
        else:
            print(
                f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] [BATCH] 30-min window complete "
                f"({len(window_pings)} fetches). No new persistent alerts met the >=2 ping & last-2-interval criteria."
            )
            state["last_batch_sent_at"] = now_sec
            window_pings = []
            window_started_at = now_sec

    state["total_fetches"] = next_fetch_num
    state["window_started_at"] = window_started_at
    state["window_pings"] = window_pings
    state["recent_pings"] = recent_pings
    state["alert_records"] = alert_records
    state["notified_uuids"] = notified_uuids
    save_state(state)
    return True


def main() -> None:
    run_once = "--once" in sys.argv
    use_mock = "--mock" in sys.argv or (os.getenv("MOCK_MODE") or "").lower() == "true"
    force_batch = "--force-batch" in sys.argv or (os.getenv("FORCE_BATCH") or "").lower() == "true"

    if not WAZE_FEED_URL and not WAZE_ROW_FEED_URL and not use_mock:
        print("[FATAL] WAZE_FEED_URL is not configured in environment or .env.", file=sys.stderr)
        sys.exit(1)

    if run_once:
        run_cycle(use_mock=use_mock, force_batch=force_batch)
        return

    print("=" * 65)
    print("🚦 Waze Live Alerts & 30-Minute Batched Telegram Service")
    print(f"Mode: {'MOCK SIMULATION' if use_mock else 'LIVE PARTNER FEED'}")
    print(f"Fetch Interval: {POLL_INTERVAL_SECONDS}s ({POLL_INTERVAL_SECONDS // 60} min)")
    print(
        f"Telegram Batch: Every {BATCH_WINDOW_MINUTES} min ({BATCH_TARGET_PINGS} fetches), "
        f"min {MIN_OCCURRENCES_IN_WINDOW} occurrences & active in last 2 intervals"
    )
    print(f"Telegram Notifications: {'ENABLED' if (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID) else 'DRY-RUN'}")
    print("=" * 65)

    while True:
        run_cycle(use_mock=use_mock, force_batch=force_batch)
        time.sleep(POLL_INTERVAL_SECONDS)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n[STOP] Stopped by user.")
