"""Additional source hygiene check; Lean compilation is still required."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parents[1]
for name in ('Certificate.lean', 'RealBounds.lean', 'CheckerCoverage.lean', 'Main.lean', 'Equality.lean'):
    source = (root / name).read_text(encoding='utf-8')
    assert not re.search(r'\bsorry\b|\badmit\b|\bnative_decide\b|(?m:^\s*axiom\b)', source), name
print('No proof placeholders, native_decide, or axiom declarations in the five sources.')
