"""Print a thinned learning curve from a PufferLib dashboard log."""
import re
import sys

text = open(sys.argv[1], errors="ignore").read()
text = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", text)
keys = sys.argv[2].split(",")
every = int(sys.argv[3]) if len(sys.argv) > 3 else 12
rows, cur = [], {}
for block in text.split("PufferLib 5.0")[1:]:
    row = {}
    for pattern, name in [(r"Steps\s+([\d.]+[KMB]?)", "steps"), (r"SPS\s+([\d.]+[KMB]?)", "sps"),
                          (r"Uptime\s+(.+?)\s{2,}", "up"), (r"Env\s+\S*\s*(\d+ms|\d+s \d+)\s+(\d+)%", "envpct")]:
        m = re.search(pattern, block)
        if m:
            row[name] = m.group(1)
    for k in keys:
        m = re.search(r"\b" + re.escape(k) + r"\s+(-?[\d.]+)", block)
        if m:
            row[k] = float(m.group(1))
    rows.append(row)
seen, out = None, []
for r in rows:
    if r.get("steps") != seen:
        out.append(r)
        seen = r.get("steps")
print(len(out), "dashboards")
for r in out[:: max(1, len(out) // every)] + out[-1:]:
    print(r)
