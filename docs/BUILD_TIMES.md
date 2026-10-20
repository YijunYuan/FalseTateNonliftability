# Build times

Wall-clock times of a clean `lake build` of this library only (`rm -rf .lake/build`; Mathlib,
FontaineWintenberger and FalseTateExtension are replayed from their caches), on a 20-core machine
with 23 GB of memory. Per-module seconds are the ones `lake build` prints; totals are from `time`.

Targets (`REFACTOR_PLAN.md` §F): every file under 30 s; the whole library under 2 min CPU; no
`set_option maxHeartbeats`, `synthInstance.maxHeartbeats` or `backward.isDefEq.respectTransparency`.

## Baseline (2026-10-20, commit 9a13337, before refactoring)

Old dependencies (Mathlib `f0b4c81`, FontaineWintenberger `7a8d63c`, FalseTateExtension `7d6876c`).
Total: 6 min 50 s wall, 290 s CPU, 41 modules, 12 400 lines. One `set_option
backward.isDefEq.respectTransparency false` (`LaurentSeries/PowerSeriesEval`).

| module | seconds |
|---|---|
| FalseTateNonliftability.FalseTate.TheoremA | 31 (58 with `lake env lean`) |
| FalseTateNonliftability.FieldOfNorms.Liftability | 15 |
| FalseTateNonliftability.FieldOfNorms.CoordinateChange | 15 |
| FalseTateNonliftability.PowerSeries.PrincipalUnitPowers | 11 |
| FalseTateNonliftability.CoefficientRing.FiniteObstruction | 10 |
| every other module (apart from the five artifacts below) | < 10 |

The log also listed `PowerSeries.PrincipalUnitIntegerPowers` 176 s, `LaurentSeries.NilpotentPower`
136 s, `LaurentSeries.OrderTopology` 136 s, `LaurentSeries.PrincipalQuotient` 135 s and
`LaurentSeries.CharacteristicP` 112 s. These five were the first leaf modules of the parallel
build and include the first load of the Mathlib `.olean` files; re-timed one at a time, each takes
2 s. They are measurement artifacts, not slow files.

## Final (2026-10-21, after the documentation phase, on top of commit 4247868)

Dependencies: Mathlib `1e75e9d`, FontaineWintenberger `1f7caa5`, FalseTateExtension `01c06ba`.
Command: `rm -rf .lake/build; time (timeout 3000 lake build 2>&1 | tee /tmp/nl-clean-build.log)`.

Total: **3 min 01 s wall, 228 s CPU** (197 s user, 30 s system), 37 modules (36 files in seven
layers and the root), 10 801 lines. No warnings, no `sorry`, no `set_option`. A no-op
`lake build` (replay only) takes 32 s wall and 4 s CPU, so almost all of the CPU time is spent on
this library. Every file is under 30 s; the slowest is `Liftability/IsLiftable` at 14 s. The sum of
the per-module times, with the six first-load artifacts replaced by their re-timed values, is
139 s; the CPU target of 2 min is not met (228 s, from 290 s).

After this build the docstring of the root file was extended by five lines (its target list now
matches `README.md`); the incremental rebuild of the root module took 1.4 s, without warnings.

As in the baseline, the six leaf modules of the `Mathlib` layer were the first modules of the
parallel build and absorbed the first load of the Mathlib `.olean` files. Re-timed one at a time
with `lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true <file>`, they
take 1.3–2.5 s.

| module | seconds |
|---|---|
| FalseTateNonliftability.Mathlib.Algebra.CharP.CharAndCard | 91 (first load; 1.3 when re-timed) |
| FalseTateNonliftability.Mathlib.NumberTheory.Padics.Continuity | 82 (first load; 1.7 when re-timed) |
| FalseTateNonliftability.Mathlib.RingTheory.AdicCompletion.Quotient | 79 (first load; 1.9 when re-timed) |
| FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition | 75 (first load; 2.1 when re-timed) |
| FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Compactness | 73 (first load; 1.6 when re-timed) |
| FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Derivative | 73 (first load; 2.5 when re-timed) |
| FalseTateNonliftability.Liftability.IsLiftable | 14 |
| FalseTateNonliftability.Liftability.FieldOfNorms | 11 |
| FalseTateNonliftability.FalseTate.RamificationNumbers | 11 |
| FalseTateNonliftability.FalseTate.TameGenerator | 10 |
| FalseTateNonliftability.CoefficientRing.Truncation | 7.4 |
| FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Topology | 7.1 |
| FalseTateNonliftability.FalseTate.Main | 6.5 |
| FalseTateNonliftability.Liftability.CoordinateFamily | 5.9 |
| FalseTateNonliftability.LaurentSeries.NormalForm | 4.1 |
| FalseTateNonliftability.CoefficientRing.NormalizedDerivative | 4.1 |
| FalseTateNonliftability.PowerSeries.PrincipalUnits | 3.7 |
| FalseTateNonliftability.LaurentSeries.Substitution | 3.3 |
| FalseTateNonliftability.CoefficientRing.Obstruction | 3.3 |
| FalseTateNonliftability.CoefficientRing.Substitution | 3.1 |
| FalseTateNonliftability.LaurentSeries.Evaluation | 3.0 |
| FalseTateNonliftability.Differential.InvariantExactDifferential | 2.9 |
| FalseTateNonliftability.Differential.ExactDifferentialLimit | 2.8 |
| FalseTateNonliftability.Differential.ApproximateInvariants | 2.6 |
| FalseTateNonliftability.PowerSeries.UnitRigidity | 2.4 |
| FalseTateNonliftability.Liftability.Defs | 2.3 |
| FalseTateNonliftability.LaurentSeries.Taylor | 2.0 |
| FalseTateNonliftability.Differential | 2.0 |
| FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Map | 1.9 |
| FalseTateNonliftability.Liftability | 1.8 |
| FalseTateNonliftability.Mathlib | 1.6 |
| FalseTateNonliftability.CoefficientRing | 1.6 |
| FalseTateNonliftability.LaurentSeries | 1.5 |
| FalseTateNonliftability.FalseTate | 1.5 |
| FalseTateNonliftability | 1.4 |
| FalseTateNonliftability.PowerSeries | 1.0 |
| FalseTateNonliftability.Liftability.CoordinateChange | 1.0 |

### Where the remaining time goes

* `Liftability/IsLiftable` (14 s): about 6 s is the instance query
  `Algebra 𝓀[K₀] (integralClosureResidueField K₀ E)`, answered nine times at 0.3–0.9 s each,
  mostly in the bodies of `residueFieldEquiv`, `residueFieldBaseFieldEquiv` and
  `integralClosureResidueFieldCongr`. Unifying FontaineWintenberger's instance
  `integralClosure_algebraMap_isLocalHom` with the `IsLocalHom` query of
  `ResidueField.instAlgebra` goes through two different semiring instance paths. A file-local
  shortcut instance gave no gain; the fix belongs in FontaineWintenberger (state that instance, or
  a shortcut `Algebra 𝓀[K] (integralClosureResidueField K L)`, in the form the query expects).
* `FalseTate/RamificationNumbers`, `FalseTate/TameGenerator` (10–11 s): every mention of
  `(τ p π).val` or `(δ p π).val` at type `L ≃ₐ[K] L` costs about 0.3 s, from unifying
  FalseTateExtension's `Gal(K_FT/ℚ_p)` with the semiring derived from the field structure; most of
  the rest is statement elaboration.
