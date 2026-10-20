# FalseTateNonliftability — notes for agents and contributors

Lean 4 (`leanprover/lean4:v4.35.0`, module system) + Mathlib formalization of Theorem A of
Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*
(`FalseTateLift.pdf`, not distributed): for a prime `p ≥ 3` and every finite totally ramified
extension `F/ℚ_p`, the action of `Gal(ℚ_p^FT/ℚ_p)` on the field of norms `X_{ℚ_p}(ℚ_p^FT)` is not
`F`-liftable in the sense of Berger (Definition 1.1). The library builds on
[FontaineWintenberger](https://github.com/YijunYuan/FontaineWintenberger) (APF extensions, the field
of norms) and [FalseTateExtension](https://github.com/YijunYuan/FalseTateExtension) (`K_FT`, `τ`,
Liu's Lemma 5.1.2, Viviani's Corollary 6.10). Design decisions and their rationale are in
`docs/REFACTOR_PLAN.md`; read the "决定" (decision) paragraphs there before changing an interface.

Code and docstrings are in English.

## Build

```sh
lake build                                   # everything
lake build FalseTateNonliftability.LaurentSeries.Substitution   # one module (and its imports)
lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true \
  FalseTateNonliftability/LaurentSeries/Substitution.lean       # check one file, writes nothing
python3 scripts/check_layers.py              # reachability and layer order (CI)
```

`lake env lean` does **not** apply the lakefile's `leanOptions`; pass them with `-D` as above.

**Never run `lake update`** and never edit anything under `.lake/packages/mathlib` (it is a symlink
shared with the local FontaineWintenberger checkout). `lake-manifest.json` is maintained by hand.
The upstream packages `.lake/packages/FontaineWintenberger` and `.lake/packages/FalseTateExtension`
are git clones; changes to them are made on the branch `nonliftability-upstream` in those clones.

**Performance red line: a single file must compile in under 30 s.** Build only the touched module
with `timeout 300 lake build <Module>`; a timeout means the design is wrong (usually an instance
being rebuilt by `letI`, a `def` whose body is a tactic block, or a `rfl` that unfolds a large
definition), not that you should wait longer. Never run a bare `lake build` of the whole library
while other agents are editing; build the modules you own.

No `sorry`, no `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` /
`backward.isDefEq.respectTransparency`, no warnings (the lakefile enables Mathlib's standard linter
set), only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Layout and layering (target)

```
FalseTateNonliftability/
  Mathlib/          upstream candidates: Mathlib names and namespaces, zero project imports
  LaurentSeries/    substitution over local Artinian principal coefficient rings, Taylor
                    expansion (§3.1), normal forms and ramification numbers (§3.2)
  PowerSeries/      principal units, p-adic powers, rigidity (§4.2)
  Differential/     invariant exact differentials (§4: Lemma 4.1, Lemma 4.2, Proposition 4.3)
  CoefficientRing/  the ring A_K, its truncations O ⧸ 𝔪^(r+1), the normalized derivative
                    (Lemma 2.4, Theorem 3.1) and the two obstructions of §6
  Liftability/      coordinate families, lifts (Definition 1.1), uniformizer independence
                    (Proposition 2.3), the field-of-norms coordinate family (Lemma 2.2)
  FalseTate/        ℚ_p^FT: ramification numbers (Proposition 5.1), the tame generator δ
                    (Lemma 5.3), Proposition 1.3 and Theorem A
FalseTateNonliftability.lean   imports one aggregate per layer
```

A layer imports only layers above it in this list. `Mathlib` … `CoefficientRing` and the abstract
part of `Liftability` (`CoordinateFamily`, `Defs`, `CoordinateChange`) import neither
FontaineWintenberger nor FalseTateExtension. (During the refactor some files still live at their
old paths; `scripts/check_layers.py` is enforced once the tree is reorganized.)

## Standing hypotheses and notation

```lean
open scoped NormedField Valued NNReal FontaineWintenberger
-- coefficient rings of Laurent substitution (fields, truncations O ⧸ 𝔪^(r+1) of a DVR):
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
-- residue fields in §3–§4:
variable {κ : Type*} [Field κ] [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
-- abstract coefficient DVR (Definition 1.1, §2, §6):
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
-- p-adic layer (FalseTateExtension conventions):
variable (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)] (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]
```

- `𝒪[K]`, `𝓀[K]` (scoped notation of `FontaineWintenberger`), `ℚ_[p]`, `ℤ_[p]`. Never spell out
  `(NormedField.valuation (K := K)).valuationSubring`, `Padic p`, `PadicInt p`, and never introduce
  file-local abbreviations (`OK`, `κK`, `O_F`, `O_0`, …) for them.
- `p` is explicit in the p-adic and coefficient-ring layers (`CharP` parameter); the general
  field-of-norms layer uses `residueChar K` as FontaineWintenberger does.
- Hypotheses that are Prop classes are instance arguments (`[Fact (Irreducible π)]`,
  `[IsAPF K L]`, `[Fact (¬ Module.Finite K L)]`, `[IsTotallyRamified K L]`); definitions never take
  proofs as value arguments. A definition that only makes sense under a hypothesis is defined for
  all inputs (junk value otherwise), and its lemmas carry the hypothesis — as Mathlib's
  `PowerSeries.subst`.
- Never install an instance with `letI`/`haveI` inside a theorem *statement*; if an instance is
  missing, add it where the type is defined.

## `local notation`

- Only inside a `section`, only for proof bodies: a public statement must not contain a
  `local notation`. A term appearing in two or more public statements is a `def`/`abbrev`.
- Never write a literal successor `(n + 1)` inside a `local notation`; write `(n + (1 : ℕ))`.

## Naming

Mathlib conventions: `lowerCamelCase` defs, `snake_case` theorems, `UpperCamelCase` types,
`IsFoo` Prop classes, conclusion in the name. No filler words ("actual", "original", "genuine",
"canonical", "literal", "prescribed", "intrinsic", "ordinary", "existing") in identifiers,
docstrings, comments or section names.

## Documentation

Module docstrings follow the Mathlib template: `# Title`, a paragraph stating the mathematics,
`## Main definitions`, `## Main results`, `## References` citing the paper by its numbering
(Yuan, Lemma 2.4; Berger 2014, Definition 1.1 in Yuan; Wintenberger, Proposition 3.3.2; Viviani,
Corollary 6.10). Declaration docstrings state the mathematics, not the proof strategy, the Lean
encoding, or what is *not* assumed. There is no blueprint: do not cite `nl:`/`ft:`/`fw:` labels.

## Working style

Discuss design changes with the author before executing them; record decisions in
`docs/REFACTOR_PLAN.md`. Dead code is deleted (git history keeps it), not archived.
