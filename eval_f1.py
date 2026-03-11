import csv, unicodedata, collections

_HAMZA_MAP = str.maketrans(
    "\u0621\u0623\u0625\u0622\u0671\u0649",
    "\u0627\u0627\u0627\u0627\u0627\u064A",
)
def norm(r):
    if not r: return ""
    r = (r or "").replace("-","").strip()
    r = unicodedata.normalize("NFD", r)
    r = "".join(c for c in r if unicodedata.category(c) != "Mn")
    r = r.translate(_HAMZA_MAP)
    return "".join(c for c in r if "\u0621" <= c <= "\u064A")

def normw(w):
    if not w: return ""
    w = unicodedata.normalize("NFD", (w or "").strip())
    return "".join(c for c in w if unicodedata.category(c) != "Mn")

gold = {}
with open("data/mishkat_word_root.csv", encoding="utf-8") as f:
    for row in csv.DictReader(f):
        w = normw(row.get("word",""))
        r = norm(row.get("root",""))
        if w and r: gold[w] = r

TP=FP=FN=0
TP2=FP2=FN2=0
errors = collections.Counter()
src_stats = collections.defaultdict(lambda: [0,0,0])

with open("out_with_sources.csv", encoding="utf-8") as f:
    for row in csv.DictReader(f):
        w = normw(row.get("word",""))
        if w not in gold: continue
        p = norm(row.get("root",""))
        g = gold[w]
        if not g: continue
        src = row.get("root_source","")
        kind = row.get("kind","")
        if not p: FN += 1
        elif p == g: TP += 1
        else: FP += 1; FN += 1
        if kind in ("noun","verb"):
            if not p: FN2 += 1
            elif p == g:
                TP2 += 1
                src_stats[src][0] += 1
            else:
                FP2 += 1; FN2 += 1
                errors[(p,g)] += 1
                src_stats[src][1] += 1

P  = TP/(TP+FP)    if TP+FP   else 0
R  = TP/(TP+FN)    if TP+FN   else 0
F1 = 2*P*R/(P+R)   if P+R     else 0
P2 = TP2/(TP2+FP2) if TP2+FP2 else 0
R2 = TP2/(TP2+FN2) if TP2+FN2 else 0
F2 = 2*P2*R2/(P2+R2) if P2+R2 else 0

print("=== F1 كامل ===  P=%.4f  R=%.4f  F1=%.4f" % (P,R,F1))
print("=== F1 noun+verb ===  P=%.4f  R=%.4f  F1=%.4f" % (P2,R2,F2))
print()
print("دقة كل مصدر (noun+verb):")
print("  %-18s %6s %6s  %7s" % ("source","TP","FP","Acc"))
for src,(tp,fp,fn) in sorted(src_stats.items(), key=lambda x:-x[1][0]):
    acc = tp/(tp+fp) if tp+fp else 0
    print("  %-18s %6d %6d  %7.3f" % (src,tp,fp,acc))
print()
print("Top أخطاء (noun+verb):")
for (p,g),c in errors.most_common(15):
    print("  %-8s -> %-8s  x%d" % (p or "-", g, c))
