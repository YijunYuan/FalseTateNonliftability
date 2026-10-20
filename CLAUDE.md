# FalseTateNonliftability — notes for agents and contributors

Lean 4 (`leanprover/lean4:v4.35.0`, module system) + Mathlib formalization of Theorem A of
Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*
(`FalseTateLift.pdf`, not distributed): for a prime `p ≥ 3` and every finite totally ramified
extension `F/ℚ_p`, the action of `Gal(ℚ_p^FT/ℚ_p)` on the field of norms `X_{ℚ_p}(ℚ_p^FT)` is not
`F`-liftable in the sense of Berger (Definition 1.1). The library builds on
[FontaineWintenberger](https://github.com/YijunYuan/FontaineWintenberger) (APF extensions, the field
of norms) and [FalseTateExtension](https://github.com/YijunYuan/FalseTateExtension) (`K_FT`, `τ`,
Liu's Lemma 5.1.2, Viviani's Corollary 6.10). `README.md` maps the paper's results to declarations.
Design decisions and their rationale are in `docs/REFACTOR_PLAN.md`; read the "决定" (decision)
paragraphs there before changing an interface.

Code and docstrings are in English.

## Build

```sh
lake build                                   # everything
lake build FalseTateNonliftability.LaurentSeries.Substitution   # one module (and its imports)
lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true \
  FalseTateNonliftability/LaurentSeries/Substitution.lean       # check one file, writes nothing
python3 scripts/check_layers.py              # reachability and layer order (CI)
```

`lake env lean` does **not** apply the lakefile's `leanOptions`; pass them with `-D` as above. It
reads the `.olean` files already built for the imports, so after changing a statement rebuild the
module with `lake build <Module>` before checking its dependents.

**Never run `lake update`** and never edit anything under `.lake/packages/mathlib` (it is a symlink
shared with the local FontaineWintenberger checkout). `lake-manifest.json` is maintained by hand.
The upstream packages `.lake/packages/FontaineWintenberger` and `.lake/packages/FalseTateExtension`
are git clones on the branch `nonliftability-upstream` (commits `1f7caa5` and `01c06ba`); changes to
them are made on that branch, and it must be pushed to GitHub before a fresh clone of this
repository builds.

**Performance red line: a single file must compile in under 30 s** (today the slowest takes 14 s;
`docs/BUILD_TIMES.md`). Build only the touched module with `timeout 300 lake build <Module>`; a
timeout means the design is wrong (usually an instance being rebuilt by `letI`, a `def` whose body
is a tactic block, or a `rfl` that unfolds a large definition), not that you should wait longer.
Run one Lean process at a time (memory is limited), and never run a bare `lake build` of the whole
library while other agents are editing; build the modules you own.

No `sorry`, no `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` /
`backward.isDefEq.respectTransparency`, no warnings (the lakefile enables Mathlib's standard linter
set), only the axioms `propext`, `Classical.choice`, `Quot.sound`. Prefer `linarith`/`omega` to
`nlinarith`, and `exact`/`rw` to `convert`.

## Layout and layering

```
FalseTateNonliftability/
  Mathlib/          upstream candidates: Mathlib names and namespaces, imports only Mathlib
    Algebra/CharP/CharAndCard            a ring with p elements has characteristic p
    NumberTheory/Padics/Continuity       ℤ_p → ℤ/pℤ is continuous; limits of p x_n
    RingTheory/AdicCompletion/Quotient   kernels of the evaluations R̂ → R ⧸ I^n
    RingTheory/LaurentSeries/Derivative  Leibniz rule, derivatives in characteristic p
    RingTheory/LaurentSeries/Topology    the T-adic topology (scoped instance)
    RingTheory/LaurentSeries/Map         coefficient maps, R((T)) ⧸ (a) ≃ (R ⧸ (a))((T))
    RingTheory/PowerSeries/Compactness   the units of κ⟦T⟧ are compact for finite κ
    RingTheory/PowerSeries/Composition   iterate, compInv, conj of power series
  LaurentSeries/    Evaluation (construction behind subst), Substitution (Lemma 2.1),
                    Taylor (Lemma 3.2), NormalForm (ramification numbers, Lemma 3.3, Thm 3.4)
  PowerSeries/      PrincipalUnits (z^c for c ∈ ℤ_p), UnitRigidity (core of Lemma 4.2)
  Differential/     InvariantExactDifferential (Lemma 4.1), ApproximateInvariants (Lemma 4.2),
                    ExactDifferentialLimit (Proposition 4.3)
  CoefficientRing/  Truncation (A_K, O ⧸ 𝔪^(r+1), layers), Substitution (subst and conj on A_K),
                    NormalizedDerivative (Lemma 2.4, Definition 2.5, Theorem 3.1),
                    Obstruction (§6, cases 1 and 2)
  Liftability/      CoordinateFamily, Defs (Lift, FiniteLift; Definition 1.1),
                    CoordinateChange (Proposition 2.3, abstract), FieldOfNorms (Lemma 2.2),
                    IsLiftable (Definition 1.1 for X_K(L), Proposition 2.3)
  FalseTate/        RamificationNumbers (Proposition 5.1), TameGenerator (δ, Lemma 5.3),
                    Main (Proposition 1.3, Theorem A)
  <Layer>.lean      one aggregate per layer, importing every file of the layer
FalseTateNonliftability.lean   imports the seven aggregates; its docstring lists the targets
```

A layer imports only layers above it in this list. `Mathlib` … `CoefficientRing` and the abstract
part of `Liftability` (`CoordinateFamily`, `Defs`, `CoordinateChange`) import neither
FontaineWintenberger nor FalseTateExtension, also through their imports. `scripts/check_layers.py`
(CI) enforces the layer order, the upstream-freeness of these layers and files (through their
import closure in the library) and that every file is imported by its aggregate; a new file must
be added to its layer's aggregate. Declarations outside the dependency closure of the paper's
results (plus the natural API of the `Mathlib/` files) are deleted.

## Standing hypotheses and notation

```lean
open scoped NormedField Valued NNReal FontaineWintenberger
-- coefficient rings of Laurent substitution (fields, truncations O ⧸ 𝔪^(r+1) of a DVR):
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
-- residue fields in §3–§4:
variable {κ : Type*} [Field κ] [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
-- abstract coefficient DVR (Definition 1.1, §2, §6):
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
-- in addition for Lemma 2.4, Theorem 3.1 and §6 (residue field 𝔽_p, p ≠ 0 in O):
variable (p : ℕ) [Fact p.Prime] [Fact (Nat.card (IsLocalRing.ResidueField O) = p)]
  [NeZero (p : O)]
-- Definition 1.1 for fields of norms:
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K]
  [IsPerfectResidueLocalField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)] [IsTotallyRamified K L]
  (F : IntermediateField ℚ_[p] (AlgebraicClosure K)) [FiniteDimensional ℚ_[p] F]
  [(baseField p K).HasSameResidueField F]
-- p-adic layer (FalseTateExtension conventions):
variable (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)] (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]
```

- `𝒪[K]`, `𝓀[K]` (scoped notation of `FontaineWintenberger`), `ℚ_[p]`, `ℤ_[p]`. Never spell out
  `(NormedField.valuation (K := K)).valuationSubring`, `Padic p`, `PadicInt p`, and never introduce
  file-local abbreviations (`OK`, `κK`, `O_F`, `O_0`, …) for them.
- `p` is explicit in the p-adic, coefficient-ring and field-of-norms layers (`CharP κ p`,
  `absoluteRamificationIdx p O`, `IsLiftable p K L F`). Over an abstract DVR `O`, "residue field
  `𝔽_p`" and "`p ≠ 0` in `O`" are the instances `[Fact (Nat.card (ResidueField O) = p)]` and
  `[NeZero (p : O)]`; `CharP` of the residue field is derived from them.
- Hypotheses that are Prop classes are instance arguments (`[Fact (Irreducible π)]`,
  `[IsAPF K L]`, `[Fact (¬ Module.Finite K L)]`, `[IsTotallyRamified K L]`,
  `[HasSameResidueField E F]`); definitions do not take proofs as value arguments. A definition
  that only makes sense under a hypothesis is defined for all inputs (junk value otherwise), and
  its lemmas carry the hypothesis — as Mathlib's `PowerSeries.subst`. A lemma whose statement
  holds without such a hypothesis does not take it (Mathlib style); where a hypothesis is implied
  by another one through a junk value, the module's Implementation notes say so (example:
  `¬ IsOfFinOrder (substEquiv f)` forces `f(0) = 0`). The exceptions, which take a proof as a
  value argument:
  1. a uniformizer of the field of norms is a pair `u hu` (`hu : valuation u = exp (-1)`), as in
     FontaineWintenberger's `FieldOfNorms.laurentEquiv K L u hu`: `FieldOfNorms.coordinateSeries`,
     `FieldOfNorms.coordinateFamily`, `IsLiftable.coordinateFamily` (Proposition 1.3 is stated for
     a uniformizer `u hu`);
  2. the order hypotheses `s ≤ r` of `Truncation.factor` and `j ≤ r` of
     `Truncation.gradedLayerEquiv`, as in Mathlib's `Ideal.Quotient.factor`;
  3. the compatibility proof of the universal property `CoefficientRing.lift`, as in Mathlib's
     `AdicCompletion.liftRingHom`;
  4. the construction behind `subst` in `LaurentSeries/Evaluation` (below).
- Never install an instance with `letI`/`haveI` inside a theorem *statement*; if an instance is
  missing, add it where the type is defined.

## Conventions established by the refactor

- **Substitution is total.** `LaurentSeries.subst G : R((T)) →ₐ[R] R((T))` is defined for every
  `G` and is the identity unless `G` is admissible (`IsAdmissible G`: the reduction of `G` modulo
  the maximal ideal has finite positive order); the lemmas carry `(hG : IsAdmissible G)`.
  `LaurentSeries.substEquiv P` (for a power series `P`) is the identity unless `P(0) = 0` and
  `P'(0)` is a unit. `PowerSeries.compInv w` is `X` unless `w'(0)` is a unit;
  `PowerSeries.conj w f = w ∘ f ∘ w^{∘-1}`, `LaurentSeries.conj`, `CoefficientRing.conj` and
  `CoordinateFamily.conj` follow the same pattern. The paper's `Q ∘ G` is `subst G Q` (the inner
  series first); `LaurentSeries.subst` and `CoefficientRing.subst` are `@[pp_nodot]`, so they are
  printed as `subst G Q`, not as `G.subst Q` (which would read as `G ∘ Q` by analogy with
  Mathlib's `PowerSeries.subst`). The inverse of `substEquiv P` is stated with `P.compInv`. The
  construction of `subst` in `LaurentSeries/Evaluation` takes a nilpotent generator `δ` of the
  maximal ideal, a decomposition `G = U + δ Y` and bounds as arguments; only
  `LaurentSeries/Substitution` uses it, and nothing downstream mentions `δ`.
- **Truncations are indexed by `r + 1`.** `Truncation O r = O ⧸ 𝔪 ^ (r + 1)`, so every `r : ℕ` is
  valid and there are no `1 ≤ r` hypotheses; the paper's `R = A ⧸ ϖ_F^(e+1) A` is
  `LaurentSeries (Truncation O e)` with `e = absoluteRamificationIdx p O = v_O(p)`.
  `CoefficientRing O` (the paper's `A_K`) is the `𝔪`-adic completion of `O((T))`, a `def` whose
  instances (`IsLocalRing`, `IsDiscreteValuationRing`, `IsAdicComplete`) are declared in
  `CoefficientRing/Truncation`. No uniformizer `ϖ` appears in statements; the layer map
  `Truncation.layer j X = ϖ⁻ʲX` (`0` if `X ∉ ϖ^j R_r`) uses a uniformizer chosen once by
  `IsDiscreteValuationRing.exists_irreducible`.
- **The `T`-adic topology is a scoped instance.** `LaurentSeries.orderTopology R` is activated by
  `open scoped LaurentSeries.OrderTopology` (high priority, so that it is also chosen over a field).
  Do not write `open scoped OrderTopology` inside `namespace LaurentSeries` (ambiguous with
  Mathlib's `OrderTopology`), do not open the scope in files that use the valued topology of
  `LaurentSeries K` (e.g. `Liftability/FieldOfNorms`), and rewrite with
  `LaurentSeries.orderTopology_eq_valued` where the two meet.
- **Residue fields.** For an algebraic, possibly infinite, extension `L/K` given as an
  intermediate field (e.g. `L ⊆ K^alg`), write `integralClosureResidueField K L`
  (FontaineWintenberger), never `ResidueField (integralClosure 𝒪[K] L)`: the structures Lean finds
  on the latter differ from FontaineWintenberger's and unifying them is slow. The ring of integers
  of a finite extension `F/ℚ_p` given as an intermediate field is `spectralIntegerRing ℚ_[p] F`,
  with residue field `ResidueField (spectralIntegerRing ℚ_[p] F)`. "Same residue field" (Berger) is
  FontaineWintenberger's class `IntermediateField.HasSameResidueField`.
- **Galois groups** of infinite extensions are `L ≃ₐ[K] L`; `τ p π` and `δ p π` are elements of
  subgroups, used through `.val`. Each mention of `(τ p π).val` at type `L ≃ₐ[K] L` costs about
  0.3 s of unification: name it once in a proof instead of restating it.
- **Numerical hypotheses are bundled.** The conditions on the ramification numbers
  `d_k = v_T(f^{∘p^k} - T) - 1` used in §6 are the structures `PowerSeries.HasRamificationGrowth`
  and `PowerSeries.HasRamificationLimit`. `PowerSeries.ramificationNumber X = -1` (the paper's
  `i = ∞`).
- **Local notations cost elaboration time** (0.1–0.9 s each in `LaurentSeries/Evaluation`); write
  terms out unless a notation saves a lot of text in proofs.

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

Module docstrings follow the Mathlib template: `# Title`, a paragraph stating the mathematics with
its notation, `## Main definitions`, `## Main results` (citing the paper's numbering),
`## Implementation notes` (only for real design choices, such as junk values or a scoped instance),
`## References` in the form "Y. Yuan, *Non-liftability of the field of norms of the p-adic false
Tate curve extension*, Lemma 2.1 (1)"; other references: Berger 2014 (Definition 1.1 in Yuan),
Wintenberger 1983, Proposition 3.3.2; Viviani 2004, Corollary 6.10; Serre, *Local Fields*, Ch. IV.
Every public declaration has a docstring. Declaration docstrings state the mathematics, not the
proof strategy, the Lean encoding, or what is *not* assumed. There is no blueprint: do not cite
`nl:`/`ft:`/`fw:` labels. Files under `Mathlib/` say that they are upstream candidates. When a
result of the paper changes declaration, update the table in `README.md` and the docstring of
`FalseTateNonliftability.lean`.

## Working style

Discuss design changes with the author before executing them; record decisions in
`docs/REFACTOR_PLAN.md`. Dead code is deleted (git history keeps it), not archived. Record the
per-module times of a clean build in `docs/BUILD_TIMES.md` after a large change.
