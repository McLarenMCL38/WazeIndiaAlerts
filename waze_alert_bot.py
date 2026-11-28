"""
Waze Partner Feed — Smart Compiled Live Map & Regional Telegram Digest (India)

Transforms noisy raw Waze Partner Feed segment reports into concise, actionable
regional & city-hub intelligence:
1. Step 4 (Barricading Removal): Completely strips multi-year "due to barricading"
   closures from both the live map and Telegram alerts.
2. Step 1 (Duplicate Compilation): Spatially & semantically merges duplicate
   reports and multi-segment closures/jams/events at the same location & type
   into a single compiled incident with combined geometry and segment count.
3. Step 3 (Long-Term Construction Corridors): Compiles highway/road construction
   works per road stretch (up to 20 km corridor) and alerts Telegram AT MOST ONCE
   using permanent stretch fingerprints.
4. Step 2 (One-Time Hazard Suppression): Tracks hazards by spatial+subtype
   location key (14-day rolling suppression) so multi-day potholes/hazards are
   never repeated after their first alert.
5. Regional & Nearest Major City Hub Intelligence: Maps every Indian coordinate
   to its Region (North/South/West/East/Central/Northeast), State, and Nearest
   Major City Hub, emitting a concise Regional & City Cumulative Digest on
   Telegram every 30 minutes (for alerts persistent across >=2 pings & active
   in the last 2 intervals).
"""

import html
import hashlib
import json
import math
import os
import re
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
STATE_FILE_PATH = BASE_DIR / "bot_state.json"


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

MIN_MAP_JAM_LEVEL = int(os.getenv("MIN_MAP_JAM_LEVEL") or "4")
MIN_MAP_JAM_DELAY_SEC = int(os.getenv("MIN_MAP_JAM_DELAY_SEC") or "180")
MAX_DETAILED_PER_BATCH = int(os.getenv("MAX_ALERTS_PER_TELEGRAM_BATCH") or "25")
INITIAL_SEED_MAX_AGE_MS = 60 * 60 * 1000

# Retention windows for one-time suppression
STANDARD_NOTIFIED_TTL_SEC = 72 * 3600       # 3 days for short-lived incidents
HAZARD_SUPPRESS_TTL_SEC = 14 * 86400        # 14 days for potholes/hazards (Step 2)
LONG_TERM_CLOSURE_TTL_SEC = 90 * 86400      # 90 days for construction stretches (Step 3)

INDIA_LAT_MIN, INDIA_LAT_MAX = 6.0, 38.0
INDIA_LON_MIN, INDIA_LON_MAX = 68.0, 98.0

CATEGORY_PRIORITY = {
    "ACCIDENT": 0,
    "ROAD_CLOSED": 1,
    "HAZARD": 2,
    "JAM": 3,
    "POLICE": 4,
}

CATEGORY_META = {
    "ROAD_CLOSED": {"icon": "⛔", "label": "Road Closure"},
    "ACCIDENT": {"icon": "💥", "label": "Accident"},
    "HAZARD": {"icon": "⚠️", "label": "Hazard"},
    "JAM": {"icon": "🚗", "label": "Standstill Jam"},
    "POLICE": {"icon": "👮", "label": "Police"},
}

JAM_LEVEL_NAMES = {
    1: "Light Traffic",
    2: "Moderate Traffic",
    3: "Heavy Traffic",
    4: "Standstill Traffic",
    5: "Road Blocked",
}

REGION_ORDER = [
    "North India",
    "West India",
    "South India",
    "East India",
    "Central India",
    "Northeast India",
]

# 68 Major Indian Metro & Regional Hubs: (Hub Name, State, Region, Lat, Lon)
INDIA_MAJOR_HUBS: list[tuple[str, str, str, float, float]] = [
    # North India
    ("Delhi NCR", "Delhi NCR", "North India", 28.6139, 77.2090),
    ("Gurugram", "Haryana", "North India", 28.4595, 77.0266),
    ("Noida", "Uttar Pradesh", "North India", 28.5355, 77.3910),
    ("Chandigarh", "Chandigarh / Punjab", "North India", 30.7333, 76.7794),
    ("Ludhiana", "Punjab", "North India", 30.9010, 75.8573),
    ("Amritsar", "Punjab", "North India", 31.6340, 74.8723),
    ("Bathinda", "Punjab", "North India", 30.2110, 74.9455),
    ("Jalandhar", "Punjab", "North India", 31.3260, 75.5762),
    ("Shimla", "Himachal Pradesh", "North India", 31.1048, 77.1734),
    ("Jammu", "Jammu & Kashmir", "North India", 32.7266, 74.8570),
    ("Srinagar", "Jammu & Kashmir", "North India", 34.0837, 74.7973),
    ("Dehradun", "Uttarakhand", "North India", 30.3165, 78.0322),
    ("Haridwar", "Uttarakhand", "North India", 29.9457, 78.1642),
    ("Haldwani", "Uttarakhand", "North India", 29.2183, 79.5130),
    ("Jaipur", "Rajasthan", "North India", 26.9124, 75.7873),
    ("Udaipur", "Rajasthan", "North India", 24.5854, 73.7125),
    ("Jodhpur", "Rajasthan", "North India", 26.2389, 73.0243),
    ("Kota", "Rajasthan", "North India", 25.2138, 75.8648),
    ("Ajmer", "Rajasthan", "North India", 26.4499, 74.6399),
    ("Lucknow", "Uttar Pradesh", "North India", 26.8467, 80.9462),
    ("Kanpur", "Uttar Pradesh", "North India", 26.4499, 80.3319),
    ("Agra", "Uttar Pradesh", "North India", 27.1767, 78.0081),
    ("Mathura", "Uttar Pradesh", "North India", 27.4924, 77.6737),
    ("Varanasi", "Uttar Pradesh", "North India", 25.3176, 82.9739),
    ("Prayagraj", "Uttar Pradesh", "North India", 25.4358, 81.8463),
    ("Meerut", "Uttar Pradesh", "North India", 28.9845, 77.7064),
    ("Bareilly", "Uttar Pradesh", "North India", 28.3670, 79.4304),
    ("Gorakhpur", "Uttar Pradesh", "North India", 26.7606, 83.3732),
    # West India
    ("Mumbai", "Maharashtra", "West India", 19.0760, 72.8777),
    ("Pune", "Maharashtra", "West India", 18.5204, 73.8567),
    ("Nashik", "Maharashtra", "West India", 19.9975, 73.7898),
    ("Chhatrapati Sambhajinagar", "Maharashtra", "West India", 19.8762, 75.3433),
    ("Kolhapur", "Maharashtra", "West India", 16.7050, 74.2433),
    ("Solapur", "Maharashtra", "West India", 17.6599, 75.9064),
    ("Ahmedabad", "Gujarat", "West India", 23.0225, 72.5714),
    ("Surat", "Gujarat", "West India", 21.1702, 72.8311),
    ("Vadodara", "Gujarat", "West India", 22.3072, 73.1812),
    ("Rajkot", "Gujarat", "West India", 22.3039, 70.8022),
    ("Panaji (Goa)", "Goa", "West India", 15.4909, 73.8278),
    # South India
    ("Bengaluru", "Karnataka", "South India", 12.9716, 77.5946),
    ("Mysuru", "Karnataka", "South India", 12.2958, 76.6394),
    ("Mangaluru", "Karnataka", "South India", 12.9141, 74.8560),
    ("Hubballi", "Karnataka", "South India", 15.3647, 75.1240),
    ("Belagavi", "Karnataka", "South India", 15.8497, 74.4977),
    ("Hyderabad", "Telangana", "South India", 17.3850, 78.4867),
    ("Warangal", "Telangana", "South India", 17.9689, 79.5941),
    ("Chennai", "Tamil Nadu", "South India", 13.0827, 80.2707),
    ("Coimbatore", "Tamil Nadu", "South India", 11.0168, 76.9558),
    ("Madurai", "Tamil Nadu", "South India", 9.9252, 78.1198),
    ("Salem", "Tamil Nadu", "South India", 11.6643, 78.1460),
    ("Tiruchirappalli", "Tamil Nadu", "South India", 10.7905, 78.7047),
    ("Visakhapatnam", "Andhra Pradesh", "South India", 17.6868, 83.2185),
    ("Vijayawada", "Andhra Pradesh", "South India", 16.5062, 80.6480),
    ("Tirupati", "Andhra Pradesh", "South India", 13.6288, 79.4192),
    ("Kochi", "Kerala", "South India", 9.9312, 76.2673),
    ("Thiruvananthapuram", "Kerala", "South India", 8.5241, 76.9366),
    ("Kozhikode", "Kerala", "South India", 11.2588, 75.7804),
    # Central India
    ("Nagpur", "Maharashtra", "Central India", 21.1458, 79.0882),
    ("Bhopal", "Madhya Pradesh", "Central India", 23.2599, 77.4126),
    ("Indore", "Madhya Pradesh", "Central India", 22.7196, 75.8577),
    ("Gwalior", "Madhya Pradesh", "Central India", 26.2183, 78.1828),
    ("Jabalpur", "Madhya Pradesh", "Central India", 23.1815, 79.9864),
    ("Jhansi", "Uttar Pradesh / MP", "Central India", 25.4484, 78.5685),
    ("Raipur", "Chhattisgarh", "Central India", 21.2514, 81.6296),
    # East India
    ("Kolkata", "West Bengal", "East India", 22.5726, 88.3639),
    ("Siliguri", "West Bengal", "East India", 26.7271, 88.3953),
    ("Patna", "Bihar", "East India", 25.5941, 85.1376),
    ("Ranchi", "Jharkhand", "East India", 23.3441, 85.3096),
    ("Jamshedpur", "Jharkhand", "East India", 22.8046, 86.2029),
    ("Bhubaneswar", "Odisha", "East India", 20.2961, 85.8245),
    # Northeast India
    ("Guwahati", "Assam", "Northeast India", 26.1445, 91.7362),
]

CONSTRUCTION_KEYWORDS = (
    "construction",
    "work in progress",
    "work is in progress",
    "work is progress",
    "working in progress",
    "black spot",
    "blackspot",
    "rectification",
    "vup",
    "lvup",
    "svup",
    "viaduct",
    "underpass",
    "overpass",
    "flyover work",
    "elevated corridor",
    "greenfield",
    "4-lane",
    "6-lane",
    "4 lane",
    "6 lane",
    "4l ",
    "6l ",
    "epc mode",
    "chainage",
    "widening",
    "resurfacing",
)

GENERIC_ROADS = {"", "unnamed road", "unnamed corridor", "service rd", "service road", "road"}


def haversine_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Fast great-circle distance in kilometers."""
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1.0, math.sqrt(a)))


def resolve_nearest_hub(lat: float, lon: float) -> tuple[str, str, str, float]:
    """Return (hub_city, state, region, dist_km) for any coordinate in India."""
    best_hub = ("India", "India", "Central India", 9999.0)
    for hub, state, region, hlat, hlon in INDIA_MAJOR_HUBS:
        # Quick degree bounding pre-check before trig when far away
        if abs(lat - hlat) > 8.0 or abs(lon - hlon) > 8.0:
            continue
        d = haversine_km(lat, lon, hlat, hlon)
        if d < best_hub[3]:
            best_hub = (hub, state, region, d)
    if best_hub[3] == 9999.0:
        for hub, state, region, hlat, hlon in INDIA_MAJOR_HUBS:
            d = haversine_km(lat, lon, hlat, hlon)
            if d < best_hub[3]:
                best_hub = (hub, state, region, d)
    return best_hub[0], best_hub[1], best_hub[2], round(best_hub[3], 1)


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
    return f"https://www.waze.com/live-map/directions?to=ll.{lat:.5f}%2C{lon:.5f}"


def build_waze_app_url(lat: float, lon: float) -> str:
    return f"https://waze.com/ul?ll={lat:.5f},{lon:.5f}&navigate=yes"


def pretty_subtype(subtype: str | None, alert_type: str | None) -> str:
    raw = (subtype or "").strip()
    if not raw:
        return ""
    prefix = (alert_type or "").strip() + "_"
    if prefix != "_" and raw.startswith(prefix):
        raw = raw[len(prefix) :]
    return raw.replace("_", " ").strip().title()


def to_latlng_list(points: list | None) -> list[list[float]]:
    coords: list[list[float]] = []
    for p in points or []:
        if isinstance(p, dict) and "x" in p and "y" in p:
            try:
                coords.append([round(float(p["y"]), 5), round(float(p["x"]), 5)])
            except (TypeError, ValueError):
                continue
    return coords


def extract_alert_latlon(alert: dict) -> tuple[float | None, float | None]:
    loc = alert.get("location")
    if isinstance(loc, dict) and "x" in loc and "y" in loc:
        try:
            return round(float(loc["y"]), 5), round(float(loc["x"]), 5)
        except (TypeError, ValueError):
            pass
    pos = alert.get("position")
    if isinstance(pos, str) and " " in pos.strip():
        parts = pos.strip().split()
        try:
            return round(float(parts[0]), 5), round(float(parts[1]), 5)
        except (TypeError, ValueError):
            pass
    return None, None


def is_barricading(subtype: str | None, description: str | None) -> bool:
    """Step 4: Identify multi-year 'road closed due to barricading' closures to drop completely."""
    combined = f"{subtype or ''} {description or ''}".lower()
    return "barricad" in combined


def is_long_term_construction(
    category: str,
    subtype: str | None,
    description: str | None,
    pub_millis: int | None,
    now_ms: int,
) -> bool:
    """Step 3: Detect long-term or construction road closures."""
    if category != "ROAD_CLOSED":
        return False
    st = (subtype or "").upper()
    if "CONSTRUCTION" in st:
        return True
    desc_low = (description or "").lower()
    if any(kw in desc_low for kw in CONSTRUCTION_KEYWORDS):
        return True
    # Closures active continuously for > 18 hours are long-term closures
    if pub_millis and (now_ms - int(pub_millis)) > 18 * 3600 * 1000:
        return True
    return False


def normalize_road_key(street: str | None) -> str:
    """Normalize highway/road names so 'NH 48', 'NH-48', and 'NH48 Service Rd' match."""
    s = (street or "").strip().lower()
    if s in GENERIC_ROADS:
        return ""
    # Extract national/state highway or expressway code if present
    m = re.search(r"\b(nh|sh|ne|ah)[\s\-]*(\d+[a-z]?)\b", s)
    if m:
        return f"{m.group(1)}-{m.group(2)}"
    s = re.sub(r"[^a-z0-9\s]", " ", s)
    s = re.sub(r"\b(near|towards|opp|opposite|flyover|underpass|bridge|service|rd|road|marg|salai|lane)\b", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def normalize_project_signature(description: str | None) -> str:
    """Extract canonical project signature for NHAI/MoRTH multi-segment descriptions."""
    d = (description or "").strip().lower()
    if not d or d in {
        "due to construction works",
        "due to hazard",
        "due to event",
        "due to object on road",
        "due to vehicle breakdown",
        "due to one way traffic",
        "due to exhibition",
    }:
        return ""
    # Strip boilerplate prefixes so minor wording variants of the same highway project merge
    d = re.sub(
        r"^(vup|lvup|underpass|black\s*spot)?\s*(long\s*term|permanent|identified\s*locations)?\s*"
        r"(rectification|construction)?\s*(of\s+\w+)?\s*(work\s+is\s+in\s+progress|work\s+in\s+progress|work\s+is\s+progress|working\s+in\s+progress)[.\s]*",
        "",
        d,
    )
    d = re.sub(r"[^a-z0-9]+", " ", d).strip()
    return d[:90] if len(d) >= 12 else ""


def classify_waze_alert(alert: dict) -> tuple[str | None, str, int]:
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
    return "HAZARD", "heavy", 3


def fetch_single_feed(feed_url: str) -> dict:
    req = urllib.request.Request(
        feed_url,
        headers={
            "User-Agent": "Mozilla/5.0 (compatible; WazePartnerClient/2.1)",
            "Accept": "application/json",
        },
    )
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode("utf-8"))


def fetch_combined_feeds() -> dict:
    urls: list[str] = []
    for candidate in (WAZE_FEED_URL, WAZE_ROW_FEED_URL):
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


def should_merge_events(a: dict, b: dict) -> bool:
    """
    Determine whether two raw events belong to the same compiled incident/stretch:
    - Must have the same high-level category (`ROAD_CLOSED`, `ACCIDENT`, `HAZARD`, `JAM`, `POLICE`).
    - Step 3 (Long-Term / Construction Closures):
      * Same non-empty highway/project signature within 45 km -> merge entire project stretch!
      * Same normalized road/highway name within 20 km -> merge entire road stretch!
      * Adjacent construction segments (even unnamed) within 3.0 km -> merge!
    - Step 1 (Duplicate Reports & Multi-Segment Incidents/Events/Jams):
      * Exact nearby location within 1.2 km of same type (merges opposite carriageways,
        intersection approaches, duplicate pothole pins, Noida unnamed event segments) -> merge!
      * Same specific event/project description within 8.0 km -> merge!
      * Same normalized road/corridor name within 5.0 km -> merge!
    """
    if a["type"] != b["type"]:
        return False

    # Quick lat/lon bounding box reject (~45 km max = ~0.42 deg)
    if abs(a["lat"] - b["lat"]) > 0.45 or abs(a["lon"] - b["lon"]) > 0.45:
        return False

    dist_km = haversine_km(a["lat"], a["lon"], b["lat"], b["lon"])

    # Same specific project/event description (e.g. "DUE TO CHANDIGARH CARNIVAL 2026" or NHAI pkg)
    proj_a = a.get("_projSig") or ""
    proj_b = b.get("_projSig") or ""
    if proj_a and proj_a == proj_b and dist_km <= 45.0:
        return True

    road_a = a.get("_roadKey") or ""
    road_b = b.get("_roadKey") or ""
    same_named_road = bool(road_a and road_a == road_b)

    # Step 3: Long-term / construction closures along a road stretch
    if a.get("isLongTerm") and b.get("isLongTerm"):
        if same_named_road and dist_km <= 20.0:
            return True
        if dist_km <= 3.0:
            return True

    # Step 1: Same road corridor within 5 km (closures, jams, hazards on same highway stretch)
    if same_named_road and dist_km <= 5.0:
        return True

    # Step 1: Duplicate reports at the same location & type (within 1.2 km; 0.8 km for distinct hazard subtypes)
    if a["type"] == "HAZARD" and a.get("subtypeLabel") != b.get("subtypeLabel"):
        return dist_km <= 0.6
    return dist_km <= 1.2


def compute_stable_tracking_key(compiled_ev: dict) -> str:
    """
    Build a location-and-corridor-stable tracking key so Waze segment UUID churn
    or repeat user taps on the same pothole/construction stretch do NOT look like
    brand-new incidents.
    """
    cat = compiled_ev["type"]
    road_key = compiled_ev.get("_roadKey") or ""
    proj_sig = compiled_ev.get("_projSig") or ""
    lat, lon = compiled_ev["lat"], compiled_ev["lon"]

    if cat == "ROAD_CLOSED" and compiled_ev.get("isLongTerm"):
        # Coarse ~10 km grid or project signature for long-term construction stretches (Step 3)
        if proj_sig:
            digest = hashlib.sha1(proj_sig.encode("utf-8")).hexdigest()[:10]
            return f"lt_proj_{digest}_{round(lat, 1)}_{round(lon, 1)}"
        if road_key:
            return f"lt_road_{road_key}_{round(lat, 1)}_{round(lon, 1)}"
        return f"lt_loc_{round(lat * 20) / 20:.2f}_{round(lon * 20) / 20:.2f}"

    if cat == "HAZARD":
        # ~1.1 km spatial grid + subtype so repeat pothole/hazard reports over days match (Step 2)
        sub = re.sub(r"[^a-z0-9]+", "", (compiled_ev.get("subtypeLabel") or "hazard").lower())[:16]
        return f"haz_{sub}_{round(lat, 2):.2f}_{round(lon, 2):.2f}"

    # Short-term closures, accidents, jams, police: ~1.1 km spatial + road key
    rk = re.sub(r"[^a-z0-9]+", "", road_key)[:16] or "pt"
    return f"inc_{cat.lower()}_{rk}_{round(lat, 2):.2f}_{round(lon, 2):.2f}"


def compile_cluster(members: list[dict]) -> dict:
    """Compile a connected cluster of 1..N raw Waze events into 1 clean cumulative event."""
    # Pick representative primary member: prefer named street, rich description, newest report
    def member_rank(m: dict) -> tuple:
        named = 0 if (m.get("street") or "").strip().lower() in GENERIC_ROADS else 1
        has_city = 0 if (m.get("city") or "") in {"", "India", "Partner Area"} else 1
        has_note = 1 if m.get("reportDescription") else 0
        return (named, has_city, has_note, int(m.get("thumbsUp") or 0), int(m.get("pubMillis") or 0))

    ranked = sorted(members, key=member_rank, reverse=True)
    primary = ranked[0]
    count = len(members)

    # Compute geographic center & span of the compiled stretch
    lats = [m["lat"] for m in members]
    lons = [m["lon"] for m in members]
    center_lat = round(sum(lats) / count, 5)
    center_lon = round(sum(lons) / count, 5)
    span_km = round(haversine_km(min(lats), min(lons), max(lats), max(lons)), 1) if count > 1 else 0.0

    # Collect polyline segments (up to 15 polylines per compiled stretch to keep JSON compact)
    multi_lines: list[list[list[float]]] = []
    for m in members:
        c = m.get("coordinates") or []
        if len(c) >= 2 and len(multi_lines) < 15:
            multi_lines.append(c)

    total_length_m = sum(int(m.get("lengthMeters") or 0) for m in members)
    max_delay_s = max(int(m.get("delaySeconds") or 0) for m in members)
    total_thumbs = sum(int(m.get("thumbsUp") or 0) for m in members)
    max_jam_lvl = max(int(m.get("jamLevel") or 0) for m in members)
    is_long_term = any(bool(m.get("isLongTerm")) for m in members)

    pub_vals = [int(m["pubMillis"]) for m in members if m.get("pubMillis")]
    latest_pub = max(pub_vals) if pub_vals else None
    earliest_pub = min(pub_vals) if pub_vals else None

    hub_city, state, region, hub_dist_km = resolve_nearest_hub(center_lat, center_lon)

    raw_city = (primary.get("city") or "").strip()
    if not raw_city or raw_city in {"India", "Partner Area"}:
        display_city = hub_city if hub_dist_km <= 35 else f"Near {hub_city} ({int(round(hub_dist_km))} km)"
    elif raw_city.lower() != hub_city.lower() and hub_dist_km <= 120:
        display_city = f"{raw_city} ({hub_city} Area)"
    else:
        display_city = raw_city

    street = primary["street"]
    if street.lower() in GENERIC_ROADS and count > 1:
        street = f"Local Road Network ({count} segments)"
    elif count > 1 and span_km >= 1.5:
        street = f"{street} ({span_km} km stretch)"

    base_desc = primary.get("desc") or ""
    if count > 1:
        compile_prefix = f"Compiled from {count} Waze reports"
        if total_length_m >= 500:
            compile_prefix += f" ({round(total_length_m / 1000, 1)} km)"
        desc = f"{compile_prefix} • {base_desc}" if base_desc else f"{compile_prefix}."
    else:
        desc = base_desc

    subtype_label = primary.get("subtypeLabel") or CATEGORY_META[primary["type"]]["label"]
    if primary["type"] == "ROAD_CLOSED" and is_long_term and "Construction" not in subtype_label and "Event" not in subtype_label:
        subtype_label = "Long-Term / Construction"

    compiled = {
        "id": primary["id"],
        "uuid": primary["uuid"],
        "entityKind": "alert" if any(m["entityKind"] == "alert" for m in members) else primary["entityKind"],
        "type": primary["type"],
        "subtypeLabel": subtype_label,
        "severity": primary["severity"],
        "jamLevel": max_jam_lvl,
        "isLongTerm": is_long_term,
        "segmentCount": count,
        "spanKm": span_km,
        "street": street,
        "city": display_city,
        "rawCity": raw_city,
        "hubCity": hub_city,
        "hubDistanceKm": hub_dist_km,
        "state": state,
        "region": region,
        "country": primary.get("country") or "IN",
        "inIndia": primary["inIndia"],
        "desc": desc,
        "reportDescription": primary.get("reportDescription") or "",
        "lat": center_lat,
        "lon": center_lon,
        "coordinates": multi_lines[0] if len(multi_lines) == 1 else [],
        "multiCoordinates": multi_lines if len(multi_lines) > 1 else [],
        "lengthMeters": total_length_m,
        "delaySeconds": max_delay_s,
        "speedKmh": primary.get("speedKmh"),
        "pubMillis": latest_pub,
        "firstPubMillis": earliest_pub,
        "thumbsUp": total_thumbs,
        "reliability": max(int(m.get("reliability") or 0) for m in members),
        "_roadKey": primary.get("_roadKey") or "",
        "_projSig": primary.get("_projSig") or "",
    }
    tracking_key = compute_stable_tracking_key(compiled)
    compiled["trackingKey"] = tracking_key
    compiled["id"] = tracking_key
    compiled["uuid"] = tracking_key
    compiled.pop("_roadKey", None)
    compiled.pop("_projSig", None)
    return compiled


def cluster_events(raw_events: list[dict]) -> list[dict]:
    """Connected-component spatial/corridor clustering partitioned by event category."""
    by_cat: dict[str, list[dict]] = {}
    for ev in raw_events:
        by_cat.setdefault(ev["type"], []).append(ev)

    compiled_all: list[dict] = []
    for cat, items in by_cat.items():
        n = len(items)
        visited = [False] * n
        # Sort by latitude so we can break early in the inner loop once delta_lat > 0.45 deg!
        items.sort(key=lambda e: e["lat"])

        for i in range(n):
            if visited[i]:
                continue
            visited[i] = True
            cluster = [items[i]]
            queue = [i]

            while queue:
                curr_idx = queue.pop()
                curr = items[curr_idx]
                # Scan backward and forward within +/- 0.45 deg latitude window
                j = curr_idx - 1
                while j >= 0 and (curr["lat"] - items[j]["lat"]) <= 0.45:
                    if not visited[j] and should_merge_events(curr, items[j]):
                        visited[j] = True
                        cluster.append(items[j])
                        queue.append(j)
                    j -= 1
                j = curr_idx + 1
                while j < n and (items[j]["lat"] - curr["lat"]) <= 0.45:
                    if not visited[j] and should_merge_events(curr, items[j]):
                        visited[j] = True
                        cluster.append(items[j])
                        queue.append(j)
                    j += 1

            compiled_all.append(compile_cluster(cluster))

    return compiled_all


def normalize_feed(
    feed: dict,
    occurrence_lookup: dict[str, int] | None = None,
    filter_light_jams: bool = True,
) -> dict:
    """
    Normalize, filter barricades (Step 4), compile duplicate & stretch segments
    (Steps 1 & 3), and enrich with Region + Nearest Major Indian City Hub.
    """
    occurrence_lookup = occurrence_lookup or {}
    now_ms = int(time.time() * 1000)
    alerts = feed.get("alerts") or []
    jams = feed.get("jams") or []
    irrs = feed.get("irregularities") or []

    raw_events: list[dict] = []
    closure_alerts_by_uuid: dict[str, dict] = {}
    removed_barricades = 0

    # 1. Process Raw Alerts
    for a in alerts:
        uid = str(a.get("uuid") or "").strip()
        if not uid:
            continue
        raw_sub = (a.get("subtype") or "").strip()
        raw_desc = (a.get("reportDescription") or "").strip()

        # Step 4: Completely remove 'road closed due to barricading'
        if is_barricading(raw_sub, raw_desc):
            removed_barricades += 1
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
        sub_label = pretty_subtype(raw_sub, a.get("type"))
        pub_ms = int(a["pubMillis"]) if a.get("pubMillis") else None
        long_term = is_long_term_construction(category, raw_sub, raw_desc, pub_ms, now_ms)

        desc_parts = [p for p in (sub_label, raw_desc) if p]
        desc = " — ".join(desc_parts) if desc_parts else f"Active {CATEGORY_META[category]['label'].lower()}."

        ev = {
            "id": f"alert_{uid}",
            "uuid": uid,
            "entityKind": "alert",
            "type": category,
            "subtypeLabel": sub_label or CATEGORY_META[category]["label"],
            "severity": severity,
            "jamLevel": jam_level,
            "isLongTerm": long_term,
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
            "pubMillis": pub_ms,
            "thumbsUp": int(a.get("nThumbsUp") or 0),
            "reliability": int(a.get("reliability") or 0),
            "_roadKey": normalize_road_key(street),
            "_projSig": normalize_project_signature(raw_desc),
        }
        raw_events.append(ev)
        if category == "ROAD_CLOSED":
            closure_alerts_by_uuid[uid] = ev

    # 2. Process Blocked Segments & Standstill Traffic Jams
    for j in jams:
        j_uid = str(j.get("uuid") or j.get("id") or "").strip()
        if not j_uid:
            continue
        lvl = int(j.get("level") or 0)
        raw_delay = int(j.get("delay") or 0)
        delay = max(0, raw_delay)
        blocking_uuid = str(j.get("blockingAlertUuid") or "").strip()
        closed = (lvl == 5) or (raw_delay == -1) or bool(blocking_uuid)

        if blocking_uuid:
            if blocking_uuid in closure_alerts_by_uuid:
                coords = to_latlng_list(j.get("line"))
                cause = closure_alerts_by_uuid[blocking_uuid]
                if not cause["coordinates"] and coords:
                    cause["coordinates"] = coords
                if not cause["lengthMeters"]:
                    cause["lengthMeters"] = int(j.get("length") or 0)
            # Note: if blocking_uuid belonged to a removed barricading alert, dropping here also hides its line!
            continue

        if filter_light_jams and not closed:
            if lvl < MIN_MAP_JAM_LEVEL or delay < MIN_MAP_JAM_DELAY_SEC:
                continue

        coords = to_latlng_list(j.get("line"))
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
        pub_ms = int(j["pubMillis"]) if j.get("pubMillis") else None

        category = "ROAD_CLOSED" if closed else "JAM"
        eff_level = 5 if closed else max(1, min(lvl, 4))
        if closed:
            desc = f"Road segment blocked ({length_m} m)."
            sub_label = "Blocked Segment"
        else:
            delay_min = max(1, round(delay / 60)) if delay >= 30 else 0
            delay_txt = f"+{delay_min} min delay" if delay_min else f"{delay}s delay"
            desc = f"{JAM_LEVEL_NAMES.get(eff_level, 'Traffic Jam')} • Avg {speed_kmh} km/h ({delay_txt})."
            sub_label = JAM_LEVEL_NAMES.get(eff_level, "Traffic Jam")

        raw_events.append({
            "id": f"jam_{j_uid}",
            "uuid": f"jam_{j_uid}",
            "entityKind": "jam",
            "type": category,
            "subtypeLabel": sub_label,
            "severity": "closed" if closed else {1: "low", 2: "moderate", 3: "heavy", 4: "critical"}[eff_level],
            "jamLevel": eff_level,
            "isLongTerm": closed and bool(pub_ms and (now_ms - pub_ms) > 18 * 3600 * 1000),
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
            "pubMillis": pub_ms,
            "thumbsUp": 0,
            "reliability": 10,
            "_roadKey": normalize_road_key(street),
            "_projSig": "",
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

        raw_events.append({
            "id": f"irr_{i_uid}",
            "uuid": f"irr_{i_uid}",
            "entityKind": "irregularity",
            "type": "JAM",
            "subtypeLabel": "Unusual Congestion",
            "severity": "critical" if lvl >= 4 else "heavy",
            "jamLevel": lvl,
            "isLongTerm": False,
            "street": street,
            "city": city,
            "country": country,
            "inIndia": in_india,
            "desc": f"Unusual congestion • {speed_kmh} km/h vs normal {reg_speed} km/h (+{delay // 60} min).",
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
            "_roadKey": normalize_road_key(street),
            "_projSig": "",
        })

    india_raw = [e for e in raw_events if e["inIndia"]]
    if INDIA_ONLY_STRICT or india_raw:
        raw_events = india_raw

    raw_count_before_compile = len(raw_events)

    # 4. Compile Duplicate Reports & Construction Stretches (Steps 1 & 3)
    events = cluster_events(raw_events)

    for e in events:
        e["occurrenceCount"] = occurrence_lookup.get(e["trackingKey"], 1)

    # Prioritize live/short-term incidents above multi-month construction on the feed
    events.sort(
        key=lambda e: (
            1 if e.get("isLongTerm") else 0,
            CATEGORY_PRIORITY.get(e["type"], 9),
            -int(e.get("pubMillis") or 0),
            -int(e.get("segmentCount") or 1),
        )
    )

    counts = {"ALL": len(events)}
    for cat in CATEGORY_PRIORITY:
        counts[cat] = sum(1 for e in events if e["type"] == cat)
    counts["LONG_TERM_CONSTRUCTION"] = sum(1 for e in events if e.get("isLongTerm"))
    counts["LIVE_SHORT_TERM"] = len(events) - counts["LONG_TERM_CONSTRUCTION"]

    # Regional & Hub summaries for the Cumulative Dashboard
    region_counts: dict[str, int] = {r: 0 for r in REGION_ORDER}
    hub_counts: dict[str, int] = {}
    for e in events:
        reg = e.get("region") or "Central India"
        region_counts[reg] = region_counts.get(reg, 0) + 1
        hub = e.get("hubCity") or ""
        if hub:
            hub_counts[hub] = hub_counts.get(hub, 0) + 1

    hubs_sorted = [h for h, _ in sorted(hub_counts.items(), key=lambda kv: (-kv[1], kv[0]))]

    bbox = None
    if events:
        lats = [e["lat"] for e in events]
        lons = [e["lon"] for e in events]
        bbox = [min(lats), min(lons), max(lats), max(lons)]

    return {
        "updatedAtMillis": now_ms,
        "updatedAtIST": format_ist(now_ms),
        "feedEndTimeMillis": feed.get("endTimeMillis"),
        "isStale": False,
        "lastGoodAtMillis": now_ms,
        "lastGoodAtIST": format_ist(now_ms),
        "compilationStats": {
            "rawEventsAfterBarricadeFilter": raw_count_before_compile,
            "compiledEvents": len(events),
            "removedBarricades": removed_barricades,
            "mergedDuplicatesAndSegments": max(0, raw_count_before_compile - len(events)),
        },
        "counts": counts,
        "regionCounts": region_counts,
        "hubCities": hubs_sorted,
        "hubCounts": hub_counts,
        "cities": hubs_sorted,
        "bbox": bbox,
        "events": events,
    }


def is_telegram_candidate(event: dict) -> bool:
    """
    Determine whether a compiled incident is eligible for Telegram batch alerts:
    - Excludes passive speed jams & irregularities unless reported as a road alert or closure.
    - Respects TELEGRAM_ALERT_TYPES filter if configured.
    """
    if event.get("entityKind") == "jam" and event.get("type") != "ROAD_CLOSED":
        return False
    if event.get("entityKind") == "irregularity":
        return False
    if TELEGRAM_ALERT_TYPES_RAW and TELEGRAM_ALERT_TYPES_RAW != "ALL":
        allowed = {x.strip() for x in TELEGRAM_ALERT_TYPES_RAW.split(",") if x.strip()}
        return event.get("type") in allowed
    return True


def retention_ttl_for_key(key: str, rec: dict | None) -> int:
    """
    Apply category-specific suppression rules:
    - Step 3: Long-term/construction road stretches (`lt_*` or `isLongTerm`) -> 90 days (alerted once).
    - Step 2: Hazards (`haz_*` or `HAZARD`) -> 14 days (potholes not repeated across days).
    - Standard short-term incidents -> 72 hours.
    """
    if key.startswith("lt_") or (rec and rec.get("isLongTerm")):
        return LONG_TERM_CLOSURE_TTL_SEC
    if key.startswith("haz_") or (rec and rec.get("type") == "HAZARD"):
        return HAZARD_SUPPRESS_TTL_SEC
    return STANDARD_NOTIFIED_TTL_SEC


def to_compact_state_record(ev: dict, now_sec: int) -> dict:
    return {
        "uuid": ev["trackingKey"],
        "trackingKey": ev["trackingKey"],
        "type": ev.get("type"),
        "subtypeLabel": ev.get("subtypeLabel"),
        "isLongTerm": bool(ev.get("isLongTerm")),
        "segmentCount": int(ev.get("segmentCount") or 1),
        "spanKm": float(ev.get("spanKm") or 0.0),
        "street": ev.get("street"),
        "city": ev.get("city"),
        "hubCity": ev.get("hubCity"),
        "region": ev.get("region"),
        "state": ev.get("state"),
        "country": ev.get("country"),
        "reportDescription": ev.get("reportDescription") or "",
        "lat": ev.get("lat"),
        "lon": ev.get("lon"),
        "pubMillis": ev.get("pubMillis"),
        "last_seen_at": now_sec,
    }


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
        "seeded": False,
        "compiled_v2_seeded": False,
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
        json.dump(state, f, ensure_ascii=False, separators=(",", ":"))
    tmp_path.replace(STATE_FILE_PATH)


def write_webpage_payload(payload: dict) -> None:
    json_text = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    ALERTS_JSON_PATH.write_text(json_text, encoding="utf-8")


def mark_existing_payload_stale() -> None:
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
    Format a concise, cumulative Regional & Nearest-Major-City Telegram Digest
    so readers can scan strictly the region/metro relevant to them in seconds.
    """
    start_str = datetime.fromtimestamp(window_start_sec, tz=timezone.utc).astimezone(IST).strftime("%I:%M %p")
    end_str = datetime.fromtimestamp(now_sec, tz=timezone.utc).astimezone(IST).strftime("%d %b %Y, %I:%M %p IST")

    total_qualified = len(qualified_alerts)
    total_raw_segments = sum(int(e.get("segmentCount") or 1) for e in qualified_alerts)

    # Build top-level category & regional summary counts
    by_type_parts = []
    for cat in ("ACCIDENT", "ROAD_CLOSED", "HAZARD", "JAM", "POLICE"):
        c = sum(1 for e in qualified_alerts if e.get("type") == cat)
        if c:
            meta = CATEGORY_META[cat]
            by_type_parts.append(f"{meta['icon']} {c} {meta['label']}{'s' if c > 1 else ''}")

    by_region_map: dict[str, list[dict]] = {}
    for ev in qualified_alerts:
        reg = ev.get("region") or "Central India"
        by_region_map.setdefault(reg, []).append(ev)

    reg_summary = " | ".join(
        f"<b>{r.replace(' India', '')}:</b> {len(by_region_map[r])}"
        for r in REGION_ORDER
        if r in by_region_map
    )

    header_lines = [
        "🇮🇳 <b>Waze India — 30-Min Regional Traffic Digest</b>",
        f"🕒 <b>{start_str} – {end_str}</b> ({total_pings_in_window} fetches)",
        f"📊 <b>{total_qualified} Compiled Incident{'s' if total_qualified != 1 else ''}</b>"
        + (f" <i>(condensed from {total_raw_segments} reports)</i>" if total_raw_segments > total_qualified else ""),
        " • ".join(by_type_parts),
        f"🗺 {reg_summary}",
        "",
    ]

    # Build regional -> nearest metro hub sections
    entry_blocks: list[str] = []
    shown_count = 0

    for reg in REGION_ORDER:
        reg_events = by_region_map.get(reg)
        if not reg_events:
            continue

        # Group within region by hubCity
        by_hub: dict[str, list[dict]] = {}
        for ev in reg_events:
            hub = ev.get("hubCity") or ev.get("city") or "Other"
            by_hub.setdefault(hub, []).append(ev)

        hub_order = sorted(by_hub.keys(), key=lambda h: (-len(by_hub[h]), h))
        reg_lines = [f"━━ 📍 <b>{html.escape(reg.upper())} ({len(reg_events)})</b> ━━"]

        for hub in hub_order:
            hub_evs = by_hub[hub]
            if shown_count >= MAX_DETAILED_PER_BATCH:
                # Cumulative one-line summary for remaining hubs if batch is unusually large
                types_short = ", ".join(
                    f"{sum(1 for x in hub_evs if x['type'] == t)} {CATEGORY_META[t]['label'].lower()}"
                    for t in CATEGORY_PRIORITY
                    if any(x["type"] == t for x in hub_evs)
                )
                reg_lines.append(f"• <b>{html.escape(hub)} Area:</b> +{len(hub_evs)} more ({html.escape(types_short)})")
                continue

            reg_lines.append(f"🏙 <b>{html.escape(hub)} Hub ({len(hub_evs)}):</b>")
            for ev in hub_evs:
                if shown_count >= MAX_DETAILED_PER_BATCH:
                    rem_in_hub = len(hub_evs) - hub_evs.index(ev)
                    reg_lines.append(f"   <i>…+{rem_in_hub} more in {html.escape(hub)}</i>")
                    break

                shown_count += 1
                meta = CATEGORY_META.get(ev["type"], {"icon": "⚠️", "label": ev["type"]})
                street = html.escape(ev.get("street") or "Unnamed Road")
                sub = html.escape(ev.get("subtypeLabel") or meta["label"])
                note = html.escape((ev.get("reportDescription") or "")[:110])
                seg_n = int(ev.get("segmentCount") or 1)
                lat = float(ev.get("lat") or 0.0)
                lon = float(ev.get("lon") or 0.0)
                live_url = html.escape(build_waze_live_map_url(lat, lon), quote=True)

                seg_tag = f" <i>[{seg_n} segs merged]</i>" if seg_n > 1 else ""
                once_tag = " <i>[1x notice]</i>" if (ev.get("isLongTerm") or ev.get("type") == "HAZARD") else ""
                line = f"  {meta['icon']} <b>{sub}:</b> {street}{seg_tag}{once_tag} — <a href=\"{live_url}\">Map ↗</a>"
                if note and note.lower() not in {"due to construction works", "due to hazard", "due to event"}:
                    line += f"\n      📝 <i>{note}</i>"
                reg_lines.append(line)

        entry_blocks.append("\n".join(reg_lines))

    # Pack into <= 3800-character Telegram HTML messages cleanly
    messages: list[str] = []
    current_msg = "\n".join(header_lines).strip()

    for block in entry_blocks:
        if len(current_msg) + len(block) + 4 > 3800 and current_msg:
            messages.append(current_msg)
            current_msg = f"🇮🇳 <b>Waze India Digest (cont.)</b>\n\n{block}"
        else:
            current_msg = f"{current_msg}\n\n{block}"

    if current_msg:
        messages.append(current_msg)

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
    messages = format_batch_messages(
        qualified_alerts,
        ping_counts,
        total_pings_in_window,
        window_start_sec,
        now_sec,
    )

    if not token or not chat_id:
        print("\n" + "=" * 60)
        print("[DRY RUN] Telegram credentials missing. Simulated 30-min regional digest:")
        for m in messages:
            print(m)
            print("-" * 60)
        return True

    telegram_url = f"https://api.telegram.org/bot{token}/sendMessage"
    all_ok = True

    for i, m in enumerate(messages):
        if i > 0:
            time.sleep(1.0)
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
                    "User-Agent": "WazeIndiaAlertsBot/2.1",
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
        print(f"[TELEGRAM] Sent 30-minute regional digest with {len(qualified_alerts)} compiled incident(s) ({len(messages)} msg).")
    return all_ok


MOCK_POOL = [
    {
        "uuid": "mock-blr-orr-1",
        "type": "ROAD_CLOSED",
        "subtype": "ROAD_CLOSED_CONSTRUCTION",
        "street": "Outer Ring Road",
        "city": "Bengaluru",
        "country": "IN",
        "location": {"x": 77.6744, "y": 12.9299},
        "reportDescription": "Metro flyover girder launching",
        "nThumbsUp": 14,
        "reliability": 9,
    },
    {
        "uuid": "mock-blr-orr-2",
        "type": "ROAD_CLOSED",
        "subtype": "ROAD_CLOSED_CONSTRUCTION",
        "street": "Outer Ring Road",
        "city": "Bengaluru",
        "country": "IN",
        "location": {"x": 77.6780, "y": 12.9330},
        "reportDescription": "Metro flyover girder launching",
        "nThumbsUp": 10,
        "reliability": 9,
    },
    {
        "uuid": "mock-almora-barricade",
        "type": "ROAD_CLOSED",
        "subtype": "ROAD_CLOSED_HAZARD",
        "street": "Unnamed Road",
        "city": "Almora",
        "country": "IN",
        "location": {"x": 79.6500, "y": 29.5900},
        "reportDescription": "DUE TO BARRICADING",
        "nThumbsUp": 1,
        "reliability": 7,
    },
    {
        "uuid": "mock-del-nh48-accident",
        "type": "ACCIDENT",
        "subtype": "ACCIDENT_MAJOR",
        "street": "Delhi-Gurgaon Expressway (NH-48)",
        "city": "Gurugram",
        "country": "IN",
        "location": {"x": 77.0895, "y": 28.4950},
        "reportDescription": "Two right lanes blocked near Cyber City exit",
        "nThumbsUp": 18,
        "reliability": 8,
    },
    {
        "uuid": "mock-pune-pothole",
        "type": "HAZARD",
        "subtype": "HAZARD_ON_ROAD_POT_HOLE",
        "street": "Mumbai-Pune Expressway",
        "city": "Pune",
        "country": "IN",
        "location": {"x": 73.8567, "y": 18.5204},
        "reportDescription": "Deep pothole in center lane",
        "nThumbsUp": 9,
        "reliability": 8,
    },
]


def build_mock_feed(fetch_index: int) -> dict:
    now_ms = int(time.time() * 1000)
    # Simulate Waze rotating pothole UUID on later fetches at the exact same spot!
    alerts = []
    for item in MOCK_POOL:
        uid = f"mock-pune-pothole-v{fetch_index}" if item["uuid"] == "mock-pune-pothole" else item["uuid"]
        alerts.append({**item, "uuid": uid, "pubMillis": now_ms - 300_000})
    return {"endTimeMillis": now_ms, "alerts": alerts, "jams": [], "irregularities": []}


def qualify_alerts_for_batch(
    window_pings: list[dict],
    alert_records: dict[str, dict],
    notified_uuids: dict[str, int],
    min_occurrences: int = MIN_OCCURRENCES_IN_WINDOW,
) -> tuple[list[dict], dict[str, int]]:
    """
    1. Still exists right now (`window_pings[-1]`).
    2. Unexpired in the last 2 ping intervals (`window_pings[-2]` & `window_pings[-1]`).
    3. Occurred >= `min_occurrences` (2) times in the 30-min window.
    4. Not already suppressed in `notified_uuids` (covers one-time hazards & construction stretches).
    """
    if len(window_pings) < 2:
        return [], {}

    ping_sets = [set(p.get("uuids") or []) for p in window_pings]
    unexpired_last_two = ping_sets[-1] & ping_sets[-2]

    ping_counts: dict[str, int] = {}
    for u in unexpired_last_two:
        ping_counts[u] = sum(1 for s in ping_sets if u in s)

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
            REGION_ORDER.index(e["region"]) if e.get("region") in REGION_ORDER else 9,
            e.get("hubCity") or "",
            CATEGORY_PRIORITY.get(e.get("type", ""), 9),
            -int(e.get("pubMillis") or 0),
        )
    )
    return qualified, ping_counts


def run_cycle(use_mock: bool = False, force_batch: bool = False) -> bool:
    state = load_state()
    now_sec = int(time.time())
    now_ms = now_sec * 1000
    next_fetch_num = int(state.get("total_fetches") or 0) + 1

    try:
        if use_mock:
            raw_feed = build_mock_feed(next_fetch_num)
        else:
            raw_feed = fetch_combined_feeds()
    except urllib.error.HTTPError as e:
        print(f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] [FETCH ERROR] HTTP {e.code}: {e.reason}", file=sys.stderr)
        mark_existing_payload_stale()
        save_state(state)
        return False
    except Exception as e:
        print(f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] [FETCH ERROR] {e}", file=sys.stderr)
        mark_existing_payload_stale()
        save_state(state)
        return False

    prelim = normalize_feed(raw_feed)
    candidate_events = [e for e in prelim["events"] if is_telegram_candidate(e)]
    current_candidate_keys = sorted({e["trackingKey"] for e in candidate_events})

    notified_uuids: dict[str, int] = {
        uid: int(ts) for uid, ts in (state.get("notified_uuids") or {}).items()
    }

    # Seed pre-existing baseline (>60m old) on initial live run or first upgrade to v2 tracking keys
    if (not state.get("seeded") or not state.get("compiled_v2_seeded")) and not use_mock:
        seeded_count = 0
        for ev in candidate_events:
            pub = ev.get("pubMillis")
            if pub and (now_ms - int(pub)) > INITIAL_SEED_MAX_AGE_MS:
                notified_uuids[ev["trackingKey"]] = now_sec
                seeded_count += 1
        state["seeded"] = True
        state["compiled_v2_seeded"] = True
        # Reset in-flight old raw-UUID window pings cleanly on key-format upgrade
        state["window_pings"] = []
        state["recent_pings"] = []
        print(
            f"[INIT] Seeded {seeded_count} pre-existing compiled stretch/hazard key(s) (>60m old); "
            f"tracking {len(candidate_events) - seeded_count} recent + all future incidents."
        )

    window_pings: list[dict] = list(state.get("window_pings") or [])
    recent_pings: list[dict] = list(state.get("recent_pings") or [])
    window_started_at = int(state.get("window_started_at") or 0)
    if window_started_at <= 0:
        window_started_at = now_sec - POLL_INTERVAL_SECONDS

    ping_entry = {"timestamp": now_sec, "uuids": current_candidate_keys}
    window_pings.append(ping_entry)
    recent_pings = (recent_pings + [ping_entry])[-max(BATCH_TARGET_PINGS, 6) :]

    recent_sets = [set(p.get("uuids") or []) for p in recent_pings]
    occurrence_lookup: dict[str, int] = {}
    for ev in prelim["events"]:
        tk = ev["trackingKey"]
        occurrence_lookup[tk] = max(1, sum(1 for s in recent_sets if tk in s))

    payload = normalize_feed(raw_feed, occurrence_lookup=occurrence_lookup)
    payload["pingCountInWindow"] = len(window_pings)
    payload["batchTargetPings"] = BATCH_TARGET_PINGS
    payload["batchWindowMinutes"] = BATCH_WINDOW_MINUTES
    write_webpage_payload(payload)

    alert_records: dict[str, dict] = dict(state.get("alert_records") or {})
    for ev in payload["events"]:
        if is_telegram_candidate(ev):
            tk = ev["trackingKey"]
            alert_records[tk] = to_compact_state_record(ev, now_sec)
            # Refresh suppression timestamp while a already-notified hazard or construction stretch stays active!
            if tk in notified_uuids and (ev.get("type") == "HAZARD" or ev.get("isLongTerm")):
                notified_uuids[tk] = now_sec

    # Prune state records & suppression keys according to category TTL (14d hazards, 90d construction, 3d standard)
    pruned_notified: dict[str, int] = {}
    for tk, ts in notified_uuids.items():
        ttl = retention_ttl_for_key(tk, alert_records.get(tk))
        if tk in alert_records or (now_sec - ts <= ttl):
            pruned_notified[tk] = ts
    notified_uuids = pruned_notified

    alert_records = {
        tk: rec
        for tk, rec in alert_records.items()
        if now_sec - int(rec.get("last_seen_at") or now_sec) <= retention_ttl_for_key(tk, rec)
    }

    elapsed_sec = now_sec - window_started_at
    is_batch_due = (
        len(window_pings) >= BATCH_TARGET_PINGS
        or (len(window_pings) >= 2 and elapsed_sec >= (BATCH_WINDOW_MINUTES * 60 - 60))
        or (force_batch and len(window_pings) >= 2)
    )

    stats = payload["compilationStats"]
    print(
        f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] Fetch #{next_fetch_num}: "
        f"{stats['compiledEvents']} compiled incidents (from {stats['rawEventsAfterBarricadeFilter']} raw, "
        f"{stats['removedBarricades']} barricades removed) | ping {len(window_pings)}/{BATCH_TARGET_PINGS}."
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
                    notified_uuids[ev["trackingKey"]] = now_sec
                state["last_batch_sent_at"] = now_sec
                window_pings = []
                window_started_at = now_sec
        else:
            print(
                f"[{datetime.now(IST).strftime('%H:%M:%S IST')}] [BATCH] 30-min window complete "
                f"({len(window_pings)} fetches). 0 new compiled incidents needed notification."
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
    print("🚦 Waze India Compiled Traffic & 30-Min Regional Digest Bot")
    print(f"Mode: {'MOCK SIMULATION' if use_mock else 'LIVE PARTNER FEED'}")
    print(f"Fetch Interval: {POLL_INTERVAL_SECONDS}s | Batch: Every {BATCH_WINDOW_MINUTES}m ({BATCH_TARGET_PINGS} pings)")
    print("=" * 65)

    while True:
        run_cycle(use_mock=use_mock, force_batch=force_batch)
        time.sleep(POLL_INTERVAL_SECONDS)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n[STOP] Stopped by user.")
