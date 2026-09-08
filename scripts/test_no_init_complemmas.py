#!/usr/bin/env python3
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def test_no_init_complemmas():
    hits = []
    for p in ROOT.rglob("*.lean"):
        if ".lake" in p.parts:
            continue
        text = p.read_text(errors="ignore")
        if "Mathlib.Init.Data.Int.CompLemmas" in text:
            hits.append(str(p.relative_to(ROOT)))
    assert hits == [], hits

if __name__ == "__main__":
    test_no_init_complemmas()
    print("ok - no Init CompLemmas")
