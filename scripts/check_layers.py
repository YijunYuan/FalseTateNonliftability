#!/usr/bin/env python3
"""Structural checks on the source tree (run in CI).

* Every `.lean` file under the library directory is reachable from the root module
  (the single `.lean` file next to `lakefile.toml`) through `import` lines.
* Every file under `<Lib>/<Layer>/` is imported by the aggregate `<Lib>/<Layer>.lean`, the root
  imports every aggregate, and a layer imports only layers listed before it.
* The layers before `Liftability` import neither `FontaineWintenberger` nor `FalseTateExtension`.

Exit status 1 on any violation."""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
root_files = [p for p in ROOT.glob('*.lean')]
assert len(root_files) == 1, f'expected one root .lean file, found {root_files}'
ROOT_FILE = root_files[0]
LIB = ROOT_FILE.stem
SRC = ROOT / LIB
# Layers in import order: each may import only earlier ones.
LAYERS = ['Mathlib', 'LaurentSeries', 'PowerSeries', 'Differential', 'CoefficientRing',
          'Liftability', 'FalseTate']
LAYER_ORDER = {layer: i for i, layer in enumerate(LAYERS)}
# Layers that must not depend on the two upstream projects.
UPSTREAM_FREE = set(LAYERS[:LAYERS.index('Liftability')])
UPSTREAM = re.compile(r'^(?:public )?import (FontaineWintenberger|FalseTateExtension)\b', re.M)
IMPORT = re.compile(rf'^(?:public )?import ({re.escape(LIB)}\.[\w.]+)', re.M)


def module(path: pathlib.Path) -> str:
    return LIB + '.' + '.'.join(path.relative_to(SRC).with_suffix('').parts)


def path_of(mod: str) -> pathlib.Path:
    return SRC.joinpath(*mod.split('.')[1:]).with_suffix('.lean')


bad: list[str] = []

# 1. reachability from the root module
seen: set[str] = set()
todo = list(IMPORT.findall(ROOT_FILE.read_text()))
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    p = path_of(m)
    if not p.exists():
        bad.append(f'{m} is imported but {p.relative_to(ROOT)} does not exist')
        continue
    todo.extend(IMPORT.findall(p.read_text()))
for f in sorted(SRC.rglob('*.lean')):
    if module(f) not in seen:
        bad.append(f'{f.relative_to(ROOT)} is not reachable from {ROOT_FILE.name}')

# 2. aggregates and layering
root_imports = set(IMPORT.findall(ROOT_FILE.read_text()))
for layer in LAYERS:
    agg = SRC / f'{layer}.lean'
    if not agg.exists():
        bad.append(f'missing aggregate {agg.relative_to(ROOT)}')
        continue
    imported = set(IMPORT.findall(agg.read_text()))
    for f in sorted((SRC / layer).rglob('*.lean')):
        if module(f) not in imported:
            bad.append(f'{f.relative_to(ROOT)} is not imported by {agg.relative_to(ROOT)}')
    for m in imported:
        if not m.startswith(f'{LIB}.{layer}.'):
            bad.append(f'{agg.relative_to(ROOT)} imports {m} outside its layer')
    if f'{LIB}.{layer}' not in root_imports:
        bad.append(f'{ROOT_FILE.name} does not import {LIB}.{layer}')
for f in sorted(SRC.rglob('*.lean')):
    parts = f.relative_to(SRC).parts
    if len(parts) < 2 or parts[0] not in LAYER_ORDER:
        if len(parts) >= 2:
            bad.append(f'{f.relative_to(ROOT)} lies outside the layers {LAYERS}')
        continue
    text = f.read_text()
    for m in re.findall(rf'^(?:public )?import {re.escape(LIB)}\.(\w+)', text, re.M):
        if m in LAYER_ORDER and LAYER_ORDER[m] > LAYER_ORDER[parts[0]]:
            bad.append(f'{f.relative_to(ROOT)} imports the later layer {m}')
    if parts[0] in UPSTREAM_FREE and UPSTREAM.search(text):
        bad.append(f'{f.relative_to(ROOT)} imports an upstream project from layer {parts[0]}')

for line in bad:
    print(line)
print(f'{len(bad)} problem(s)' if bad else 'reachability and layering OK')
sys.exit(1 if bad else 0)
