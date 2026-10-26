# FalseTateNonliftability

Lean 4 + Mathlib formalization of Y. Yuan, *Non-liftability of the field of norms of the p-adic
false Tate curve extension*. Let `p ≥ 3` be a prime and

```
ℚ_p^FT = ⋃ₙ ℚ_p(ζ_{pⁿ}, p^{1/pⁿ})
```

the false Tate curve extension, with Galois group `Γ = Gal(ℚ_p^FT/ℚ_p)`, field of norms
`X = X_{ℚ_p}(ℚ_p^FT)` and residue field `𝔽_p`. Let `τ` be the generator of
`Gal(ℚ_p^FT/ℚ_p(ζ_{p^∞})) ≅ ℤ_p` with `τ(p^{1/pⁿ}) = ζ_{pⁿ} p^{1/pⁿ}` and `δ` the tame generator
of `Gal(ℚ_p^FT/ℚ_p(p^{1/p^∞})) ≅ ℤ_pˣ`. For a uniformizer `u` of `X` and `g ∈ Γ`, `f_{g,u} ∈ T 𝔽_p⟦T⟧`
is the coordinate series with `ev_u(f_{g,u}) = g(u)`, where `ev_u : 𝔽_p((T)) ≅ X` sends `T` to `u`.

The library builds on [FontaineWintenberger](https://github.com/YijunYuan/FontaineWintenberger)
(arithmetically profinite extensions, the field of norms `X_K(L)` and the action of `Gal(L/K)` on
it) and [FalseTateExtension](https://github.com/YijunYuan/FalseTateExtension) (`ℚ_p^FT`, `τ`,
Liu's Lemma 5.1.2, Viviani's Corollary 6.10).

## What is formalized

**Theorem A** (`FalseTateNonliftability.not_isLiftable_falseTate`). For every finite totally
ramified extension `F/ℚ_p`, the action of `Γ` on `X` is not `F`-liftable in the sense of Berger
(Definition 1.1): with `𝒪_F` the ring of integers of `F`, `𝔪_F` its maximal ideal and `A` the
`𝔪_F`-adic completion of `𝒪_F((T))`, there are no `P` and `(F_g)_{g ∈ Γ}` in `A` whose reductions
modulo `𝔪_F` are `P̄ = T^p` and `F̄_g = f_{g,u}` for a uniformizer `u` of `X` (by Proposition 2.3,
the choice of `u` does not matter), such that `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}` for all
`g, h ∈ Γ`.

```lean
theorem FalseTateNonliftability.not_isLiftable_falseTate (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)]
    (F : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] F]
    [IsTotallyRamified ℚ_[p] F] :
    ¬ IsLiftable p ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) F
```

**Proposition 1.3** (`FalseTateNonliftability.not_finiteLiftable_falseTate`). Let `F/ℚ_p` be finite
and totally ramified with absolute ramification index `e = v_F(p)`, and let `u` be any uniformizer
of `X`. There are no `P, F_τ, F_δ ∈ (𝒪_F ⧸ 𝔪_F^(e+1))((T)) = A ⧸ 𝔪_F^(e+1) A` with reductions
`P̄ = T^p`, `F̄_τ = f_{τ,u}`, `F̄_δ = f_{δ,u}` such that `F_τ ∘ P = P ∘ F_τ` and
`F_δ ∘ P = P ∘ F_δ`. There is no composition law, and only the two elements `τ, δ` of `Γ` occur:

```lean
theorem FalseTateNonliftability.not_finiteLiftable_falseTate (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)]
    (F : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] F]
    [IsTotallyRamified ℚ_[p] F]
    {u : FieldOfNorms ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p]))}
    (hu : FieldOfNorms.valuation ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) u =
      WithZero.exp (-1 : ℤ)) :
    ¬ CoordinateFamily.FiniteLiftable
      (IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) F u hu)
      {(τ p (p : 𝒪[ℚ_[p]])).val, (δ p (p : 𝒪[ℚ_[p]])).val}
      (absoluteRamificationIdx p (spectralIntegerRing ℚ_[p] F))
```

Both statements are proved more generally for `ℚ_p(π^{1/p^∞}, ζ_{p^∞})` and every uniformizer `π`
of `ℚ_p` (`not_isLiftable_falseTateExtension`, `not_finiteLiftable_falseTateExtension`). As in the
abstract of the paper, over `F = ℚ_p` the Kummer generator alone has no lift modulo `p²` commuting
with a lift of Frobenius (`not_finiteLiftable_kummerGenerator_bot`).

`IsLiftable p K L F` is Definition 1.1 in the generality of the paper: `K/ℚ_p` finite, `L ⊆ K^alg`
an infinite separable totally ramified APF extension of `K` (`[IsAPF K L]`,
`[Fact (¬ Module.Finite K L)]`, `[IsTotallyRamified K L]`) acted on by `Aut(L/K)`, and
`F ⊆ K^alg` a finite extension of `ℚ_p` with the same residue field as `K`
(`[(baseField p K).HasSameResidueField F]`); `F` need not contain `K`. It depends on `(K, L, F)`
only: by Proposition 2.3 (`isLiftable_iff_uniformizer`) every uniformizer of `X_K(L)` gives the
same condition.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## The paper's results

All names are in the namespace `FalseTateNonliftability` unless they start with `LaurentSeries.`,
`PowerSeries.` or `FalseTateExtension.`; modules are relative to `FalseTateNonliftability/`.

| Paper | Declaration (module) |
|---|---|
| Definition 1.1 (Berger) | `IsLiftable` (`Liftability/IsLiftable`); `CoordinateFamily.Lift`, `CoordinateFamily.Liftable` (`Liftability/Defs`); the ring `A_K`: `CoefficientRing O`, a complete DVR with residue field `κ((T))`: instances `CoefficientRing.isDiscreteValuationRing`, `CoefficientRing.isAdicComplete`, `CoefficientRing.residueFieldEquiv` (`CoefficientRing/Truncation`) |
| Lemma 1.2 (3) | `tameGenerator`, notation `δ`; `padicCyclotomicCharacter_tameGenerator`, `orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator`; the relation `δ τ = τ^{χ(δ)} δ`: `tameGenerator_mul_kummerGenerator`, for every `σ ∈ Gal(ℚ_p^FT/ℚ_p(p^{1/p^∞}))`: `falseTateKummerFixing_mul_kummerGenerator` (`FalseTate/TameGenerator`); `τ` is `FalseTateExtension.kummerGenerator`. Lemma 1.2 (1), (2) are in FalseTateExtension |
| **Proposition 1.3** | `not_finiteLiftable_falseTate`, `not_finiteLiftable_falseTateExtension`, `not_finiteLiftable_kummerGenerator_bot`; with `δ` replaced by any `σ` whose character `χ(σ) mod p` has order `p - 1`, for instance any generator of the torsion subgroup in Lemma 1.2 (3): `not_finiteLiftable_falseTateExtension_of_orderOf` (`FalseTate/Main`); the data: `CoordinateFamily.FiniteLift`, `CoordinateFamily.FiniteLiftable` (`Liftability/Defs`); over an abstract DVR: `Truncation.false_of_commute` (`CoefficientRing/Obstruction`) |
| Lemma 2.1 | (1) `LaurentSeries.subst`, `LaurentSeries.subst_unique`; (2) `LaurentSeries.subst_comp_subst`, `LaurentSeries.derivative_subst`; (3) `LaurentSeries.substEquiv_symm` (`LaurentSeries/Substitution`), `PowerSeries.map_compInv` (`Mathlib/RingTheory/PowerSeries/Composition`); over `A_K`: `CoefficientRing.subst_X`, `CoefficientRing.subst_unique`, `CoefficientRing.subst_comp_subst` (`CoefficientRing/Substitution`) |
| Lemma 2.2 | `FieldOfNorms.coordinateSeries`, `FieldOfNorms.coordinateFamily`; (1) `FieldOfNorms.isUnit_coeff_one_coordinateSeries`; (2) `FieldOfNorms.aut_laurentEquiv`; (3) `FieldOfNorms.coordinateSeries_mul`; (4) `FieldOfNorms.coordinateSeries_eq_conj` (`Liftability/FieldOfNorms`) |
| **Proposition 2.3** | `isLiftable_iff_uniformizer`, `isLiftable_iff_exists_uniformizer`, `isLiftable_iff_forall_uniformizer`, `IsLiftable.liftable_coordinateFamily_iff`; modulo `𝔪_F^(r+1)`, for a Frobenius lift commuting with lifts of a prescribed collection of elements (without the composition law, the form used in Proposition 1.3): `IsLiftable.finiteLiftable_coordinateFamily_iff` (`Liftability/IsLiftable`); the statement modulo `𝔪_F^(r+1)` with the composition law is not formalized; for an abstract coordinate family: `CoordinateFamily.liftable_conj_iff`, `CoordinateFamily.finiteLiftable_conj_iff` (`Liftability/CoordinateChange`) |
| Lemma 2.4 | `Truncation.derivative_ne_zero`, `Truncation.derivativeLevel_eq_iff`, `Truncation.one_le_derivativeLevel`, `Truncation.derivativeLevel_le`; (1) `Truncation.subst_normalizedDerivative_of_commute`; (2) `Truncation.mapRingHom_residue_conj`, `Truncation.derivativeLevel_conj`, `Truncation.subst_normalizedDerivative_conj`, `Truncation.order_normalizedDerivative_conj`; (3) `Truncation.exists_normalizedDerivative_eq_derivative`, `Truncation.exists_normalizedDerivative_eq_single_add_derivative` (with the constant `c = p/ϖ^e mod 𝔪`), `Truncation.coeff_layer_C_natCast_ne_zero` (`c ≠ 0`), `Truncation.derivative_normalizedDerivative_ne_zero`, `Truncation.order_derivative_normalizedDerivative_le` (`CoefficientRing/NormalizedDerivative`) |
| Definition 2.5 | `Truncation.derivativeLevel`, `Truncation.normalizedDerivative` (`CoefficientRing/NormalizedDerivative`); the layers `ϖ⁻ʲX`: `Truncation.layer` (`CoefficientRing/Truncation`) |
| Theorem 3.1 | `Truncation.order_normalizedDerivative_le`; the series computation `LaurentSeries.order_le_of_subst_eq_derivative_pow_mul` (`CoefficientRing/NormalizedDerivative`) |
| Lemma 3.2 | `LaurentSeries.subst_sub_mem_orderAddSubgroup`, `LaurentSeries.subst_sub_leadingTerm_mem` (`LaurentSeries/Taylor`) |
| Lemma 3.3 | `PowerSeries.ramificationNumber_iterate_eq_of_resonant` (`LaurentSeries/NormalForm`) |
| Theorem 3.4 | `PowerSeries.exists_normalForm` (`LaurentSeries/NormalForm`) |
| Lemma 4.1 | `LaurentSeries.exists_exact_invariant_of_weighted_identities` (`Differential/InvariantExactDifferential`) |
| Lemma 4.2 | `LaurentSeries.padic_limit_order_eq_zero_of_approximate_invariance` (`Differential/ApproximateInvariants`); the rigidity `(f/T)^m (U ∘ f) = U ⇒ m = 0`: `PowerSeries.eq_zero_of_principalUnitPow_mul_subst_eq` (`PowerSeries/UnitRigidity`) |
| Proposition 4.3 | `LaurentSeries.padic_ramification_limit_eq_of_invariant_exact_differential` (`Differential/ExactDifferentialLimit`) |
| Proposition 5.1 | (5.1) `ramificationNumber_kummerGenerator_pow`; (2) `kummerRamificationBreak_tendsto_atTop`, `kummerRamificationBreak_tendsto_padic`, `kummerRamificationLimit_notMem_range_intCast` (`FalseTate/RamificationNumbers`); (1) `FalseTateExtension.kummerRamificationBreak_succ_dvd`, `FalseTateExtension.kummerRamificationBreak_growth`; as used in §6: `hasRamificationLimit_coordinateFamily_series_kummerGenerator` (`FalseTate/Main`) |
| Lemma 5.3 | `coeff_one_coordinateSeries_tameGenerator`, `orderOf_coeff_one_coordinateSeries_tameGenerator`; for every `σ ∈ Gal(ℚ_p^FT/ℚ_p(p^{1/p^∞}))`: `coeff_one_coordinateSeries_falseTateKummerFixing`, `orderOf_coeff_one_coordinateSeries_falseTateKummerFixing` (`FalseTate/TameGenerator`) |
| §6, case 1 (`s(P) = e`) | `Truncation.derivativeLevel_lt_absoluteRamificationIdx` (`CoefficientRing/Obstruction`) |
| §6, case 2 (`s(P) < e`) | `Truncation.absoluteRamificationIdx_le_derivativeLevel` (`CoefficientRing/Obstruction`) |
| **Theorem A** | `not_isLiftable_falseTate`, `not_isLiftable_falseTateExtension` (`FalseTate/Main`) |

Remark 5.2 (the corrected lower index in Viviani's Corollary 6.10) is target 6 of
FalseTateExtension. Remarks 2.6 and 6.1 are not formalized.

## Layout

```
FalseTateNonliftability/
  Mathlib/          upstream candidates: Mathlib names and namespaces, no project imports
  LaurentSeries/    substitution over local Artinian principal coefficient rings (Lemma 2.1),
                    Taylor expansions (Lemma 3.2), ramification numbers and normal forms
                    (Lemma 3.3, Theorem 3.4)
  PowerSeries/      principal units: p-adic powers, rigidity (§4.2)
  Differential/     invariant exact differentials (Lemma 4.1, Lemma 4.2, Proposition 4.3)
  CoefficientRing/  the ring A_K, its truncations O ⧸ 𝔪^(r+1), substitution and conjugation,
                    the normalized derivative (Lemma 2.4, Theorem 3.1), the two cases of §6
  Liftability/      total ramification and residue field interfaces, coordinate families
                    (Lemma 2.2), lifts (Definition 1.1), independence of the uniformizer
                    (Proposition 2.3)
  FalseTate/        ℚ_p^FT: ramification numbers (Proposition 5.1), the tame generator
                    (Lemma 5.3), Proposition 1.3 and Theorem A
FalseTateNonliftability.lean   imports one aggregate per layer
```

A layer imports only layers above it in this list. The layers `Mathlib` to `CoefficientRing`
import neither FontaineWintenberger nor FalseTateExtension; the abstract part of `Liftability`
(`CoordinateFamily`, `Defs`, `CoordinateChange`) does not use them either.
`scripts/check_layers.py` (run in CI) checks the layer order, that these layers and files do not
depend on the upstream projects (through their whole import closure in the library), and that
every file is imported by its layer's aggregate.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check_layers.py
```

The library contains no `sorry` and no `set_option`, and builds without warnings under Mathlib's
standard linter set. A clean build of the library takes 3 min wall-clock time on 20 cores, and no
file takes more than 15 s (`docs/BUILD_TIMES.md`).

## Dependencies

| package | version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa` |
| FontaineWintenberger | `7f43e30506d355ea81b0ea2bbb0b07680203ccec` |
| FalseTateExtension | `2040c7ea259f8a10e326d55f5771959e0851328b` |

The commits are pinned in `lakefile.toml` and `lake-manifest.json`. The classes
`FontaineWintenberger.IsTotallyRamified` and `IntermediateField.HasSameResidueField`, together
with the residue field abbreviation `FontaineWintenberger.integralClosureResidueField`, are
provided by this library in `Liftability/TotallyRamified`. The instances for total ramification
of the false Tate extension and for `p` being a uniformizer are in
`FalseTate/RamificationNumbers` and `FalseTate/Main`, respectively.

See `CLAUDE.md` for conventions and standing hypotheses, `docs/REFACTOR_PLAN.md` for the design
and its execution log, `docs/MATHLIB_REUSE.md` for what is taken from Mathlib and the upstream
libraries, and `docs/BUILD_TIMES.md` for compile times.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
* J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. ENS 16 (1983), 59–89.
* J.-P. Serre, *Local Fields*, Chapter IV.
* F. Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, J. Théor.
  Nombres Bordeaux 16 (2004), 779–816.
* T. Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*,
  Compos. Math. 144 (2008), 61–88.

The papers are not distributed with this repository.

## License

Apache 2.0, see `LICENSE`.
