/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateNonliftability.Mathlib.RingTheory.AdicCompletion.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The coefficient ring `A`, its truncations and their layers

Let `O` be a local ring with maximal ideal `𝔪` and residue field `κ`; in Yuan, `O = 𝒪_F` is the
ring of integers of a finite extension `F` of `ℚ_p`, a discrete valuation ring with uniformizer
`ϖ`. The coefficient ring `A` of Yuan, Definition 1.1, is the `ϖ`-adic completion of `O⟦T⟧[1/T]`,
that is, the `𝔪`-adic completion of the ring `O((T))` of Laurent series. If `𝔪` is principal,
then for every `r ≥ 0` the quotient `A ⧸ 𝔪 ^ (r + 1) A` is the ring `(O ⧸ 𝔪 ^ (r + 1))((T))` of
Laurent series over the truncation `O ⧸ 𝔪 ^ (r + 1)`, and `A` is the inverse limit of these rings;
for `r = e = v_ϖ(p)` this is the ring `R = A ⧸ ϖ ^ (e + 1) A` of Yuan, §1.5. In this case `A` is
a local ring, complete for its maximal ideal `𝔪 A`, with residue field `κ((T))`, and if `O` is a
discrete valuation ring then so is `A`, with uniformizer `ϖ`. These facts are the description of
`A` in Definition 1.1; the proofs of Proposition 1.4 and Theorem A do not use them.

Let `O` be a discrete valuation ring and `R_r = (O ⧸ 𝔪 ^ (r + 1))((T))`. The ideals
`𝔪 ^ j R_r = ϖ ^ j R_r` of Laurent series with coefficients in `𝔪 ^ j` decrease from `R_r` for
`j = 0` to `0` for `j = r + 1`. For `j ≤ r`, multiplication by `ϖ ^ j` induces an isomorphism of
`O`-modules `Λ_j : κ((T)) ≃ ϖ ^ j R_r ⧸ ϖ ^ (j + 1) R_r` (Yuan, §2.2). For `X ∈ ϖ ^ j R_r`, the
series `ϖ⁻ʲ X ∈ κ((T))` is the preimage of `X mod ϖ ^ (j + 1) R_r` under `Λ_j`. It is computed
coefficientwise, it satisfies $\varpi^{-j}(XZ) = \varpi^{-j}X \cdot \bar{Z}$, where $\bar{Z}$ is the
reduction of `Z` to `κ((T))`. It commutes with every algebra endomorphism of `R_r` that reduces
to an endomorphism of `κ((T))`.

## Main definitions

* `Truncation O r`: the truncation `O ⧸ 𝔪 ^ (r + 1)`.
* `Truncation.factor O hsr`, `Truncation.residue O r`: the reductions
  `O ⧸ 𝔪 ^ (r + 1) → O ⧸ 𝔪 ^ (s + 1)` for `s ≤ r` and `O ⧸ 𝔪 ^ (r + 1) → κ`.
* `CoefficientRing O`: the `𝔪`-adic completion `A` of `O((T))` (Yuan, Definition 1.1).
* `CoefficientRing.reduction O r`: the reduction `A → (O ⧸ 𝔪 ^ (r + 1))((T))`.
* `CoefficientRing.residue O`: the reduction `A → κ((T))`.
* `CoefficientRing.lift f hf`: the map into `A` induced by a compatible family of maps into the
  rings `(O ⧸ 𝔪 ^ (r + 1))((T))`.
* `Truncation.layerIdeal O r j`: the ideal `𝔪 ^ j R_r`.
* `Truncation.GradedLayer O r j`: the `O`-module `ϖ ^ j R_r ⧸ ϖ ^ (j + 1) R_r`.
* `Truncation.gradedLayerEquiv O r j hj`: the isomorphism `Λ_j` (Yuan, §2.2).
* `Truncation.layer j X`: the series `ϖ⁻ʲ X ∈ κ((T))` (Yuan, §2.2).

## Main results

* `Truncation.isArtinianRing`, `Truncation.isPrincipalIdealRing`: for a discrete valuation ring
  `O`, the truncations are local Artinian principal ideal rings.
* `CoefficientRing.ker_reduction`: the kernel of `A → (O ⧸ 𝔪 ^ (r + 1))((T))` is
  `𝔪 ^ (r + 1) A`.
* `CoefficientRing.ext_reduction`: an element of `A` is determined by its reductions.
* `CoefficientRing.isLocalRing`, `CoefficientRing.maximalIdeal_eq_map`: `A` is a local ring with
  maximal ideal `𝔪 A` (Yuan, Definition 1.1).
* `CoefficientRing.isAdicComplete`: `A` is complete for its maximal ideal (Yuan,
  Definition 1.1).
* `CoefficientRing.residueFieldEquiv`: the residue field of `A` is `κ((T))` (Yuan,
  Definition 1.1).
* `CoefficientRing.isDiscreteValuationRing`, `CoefficientRing.irreducible_algebraMap`: if `O` is
  a discrete valuation ring, so is `A`, and a uniformizer of `O` is a uniformizer of `A` (Yuan,
  Definition 1.1).
* `Truncation.layer_eq_zero_iff`: for `X ∈ ϖ ^ j R_r`, `ϖ⁻ʲ X = 0` if and only if
  `X ∈ ϖ ^ (j + 1) R_r`.
* `Truncation.layer_mul`: $\varpi^{-j}(XZ) = \varpi^{-j}X \cdot \bar{Z}$.
* `Truncation.coeff_layer_eq_zero_iff`, `Truncation.coeff_layer_eq_of_coeff_eq_mul`: the
  coefficients of `ϖ⁻ʲ X`.
* `Truncation.layer_algHom`: `ϖ⁻ʲ (E X) = E' (ϖ⁻ʲ X)` if `E` reduces to `E'`.

## Implementation notes

* The truncation is indexed so that `Truncation O r = O ⧸ 𝔪 ^ (r + 1)` is a nonzero ring for every
  `r : ℕ`; the ring `R` of Yuan, §1.5, is `LaurentSeries (Truncation O e)`, and its layers
  `ϖ ^ j R` are `layerIdeal O e j` with `0 ≤ j ≤ e + 1`.
* The instances `Truncation.isLocalRing`, `Truncation.isArtinianRing` and
  `Truncation.isPrincipalIdealRing` place the truncations in the class of coefficient rings of
  `LaurentSeries.subst` (local Artinian principal ideal rings).
* `Λ_j` depends on the uniformizer: replacing `ϖ` by `u ϖ` multiplies `ϖ⁻ʲ X` by the residue of
  `u⁻ʲ`. A uniformizer of `O` is chosen once by `IsDiscreteValuationRing.exists_irreducible`, so
  it does not appear in the statements.
* `layer j X` is defined for all `j` and `X`, with value `0` if `X ∉ ϖ ^ j R_r` or `r < j`; its
  lemmas assume `X ∈ ϖ ^ j R_r`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Definition 1.1, §1.5 and §2.2.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/

@[expose] public section

noncomputable section

/-! ### The truncations and the coefficient ring -/

section Truncations

namespace FalseTateNonliftability

open LaurentSeries
open IsLocalRing (maximalIdeal ResidueField)

variable (O : Type*) [CommRing O] [IsLocalRing O]

/-- The truncation `O ⧸ 𝔪 ^ (r + 1)` of a local ring `O` with maximal ideal `𝔪`. -/
abbrev Truncation (r : ℕ) : Type _ := O ⧸ maximalIdeal O ^ (r + 1)

/-- The ideal `𝔪 O((T))` of Laurent series over `O` generated by the maximal ideal of `O`. -/
abbrev CoefficientRing.adicIdeal : Ideal (LaurentSeries O) :=
  (maximalIdeal O).map (HahnSeries.C : O →+* LaurentSeries O)

namespace Truncation

/-- The reduction `O → O ⧸ 𝔪 ^ (r + 1)`. -/
abbrev mk (r : ℕ) : O →+* Truncation O r := Ideal.Quotient.mk _

/-- The reduction `O → O ⧸ 𝔪 ^ (r + 1)` is surjective. -/
theorem mk_surjective (r : ℕ) : Function.Surjective (mk O r) := Ideal.Quotient.mk_surjective

/-- `𝔪 ^ (r + 1) ⊆ 𝔪`. -/
theorem maximalIdeal_pow_le (r : ℕ) : maximalIdeal O ^ (r + 1) ≤ maximalIdeal O :=
  Ideal.pow_le_self r.succ_ne_zero

/-- `O ⧸ 𝔪 ^ (r + 1)` is a nonzero ring. -/
instance nontrivial (r : ℕ) : Nontrivial (Truncation O r) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top (maximalIdeal_pow_le O r))

/-- `O ⧸ 𝔪 ^ (r + 1)` is a local ring. -/
instance isLocalRing (r : ℕ) : IsLocalRing (Truncation O r) :=
  .of_surjective' (mk O r) (mk_surjective O r)

/-- The maximal ideal of `O ⧸ 𝔪 ^ (r + 1)` is the image of `𝔪`. -/
theorem maximalIdeal_eq_map (r : ℕ) :
    maximalIdeal (Truncation O r) = (maximalIdeal O).map (mk O r) :=
  (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le (mk_surjective O r)
    (by rw [Ideal.mk_ker]; exact maximalIdeal_pow_le O r))).symm

/-- The `(r + 1)`-st power of the maximal ideal of `O ⧸ 𝔪 ^ (r + 1)` is zero. -/
theorem maximalIdeal_pow_eq_bot (r : ℕ) : maximalIdeal (Truncation O r) ^ (r + 1) = ⊥ := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_quotient_self]

/-- For `k ≤ r + 1`, the image of `x ∈ O` in `O ⧸ 𝔪 ^ (r + 1)` lies in the `k`-th power of the
maximal ideal if and only if `x ∈ 𝔪 ^ k`. -/
theorem mk_mem_maximalIdeal_pow_iff {k r : ℕ} (hk : k ≤ r + 1) (x : O) :
    mk O r x ∈ maximalIdeal (Truncation O r) ^ k ↔ x ∈ maximalIdeal O ^ k := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_quotient_iff_mem (Ideal.pow_le_pow_right hk)

/-- If `O` is Noetherian, then `O ⧸ 𝔪 ^ (r + 1)` is Artinian. -/
instance isArtinianRing [IsNoetherianRing O] (r : ℕ) : IsArtinianRing (Truncation O r) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨r + 1, maximalIdeal_pow_eq_bot O r⟩

/-- If `O` is a principal ideal ring, so is `O ⧸ 𝔪 ^ (r + 1)`. -/
instance isPrincipalIdealRing [IsPrincipalIdealRing O] (r : ℕ) :
    IsPrincipalIdealRing (Truncation O r) :=
  .of_surjective (mk O r) (mk_surjective O r)

/-- The reduction `O ⧸ 𝔪 ^ (r + 1) → O ⧸ 𝔪 ^ (s + 1)` for `s ≤ r`. -/
def factor {s r : ℕ} (hsr : s ≤ r) : Truncation O r →+* Truncation O s :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hsr))

/-- The residue map `O ⧸ 𝔪 ^ (r + 1) → κ = O ⧸ 𝔪`. -/
def residue (r : ℕ) : Truncation O r →+* ResidueField O :=
  Ideal.Quotient.factor (maximalIdeal_pow_le O r)

/-- The residue of the image of `x ∈ O` in `O ⧸ 𝔪 ^ (r + 1)` is the residue of `x`. -/
@[simp]
theorem residue_mk (r : ℕ) (x : O) : residue O r (mk O r x) = IsLocalRing.residue O x := rfl

/-- The composite `O → O ⧸ 𝔪 ^ (r + 1) → κ` is the residue map of `O`. -/
@[simp]
theorem residue_comp_mk (r : ℕ) : (residue O r).comp (mk O r) = IsLocalRing.residue O :=
  RingHom.ext fun _ ↦ rfl

/-- The residue map `O ⧸ 𝔪 ^ (r + 1) → κ` is surjective. -/
theorem residue_surjective (r : ℕ) : Function.Surjective (residue O r) :=
  Ideal.Quotient.factor_surjective _

/-- The kernel of the residue map `O ⧸ 𝔪 ^ (r + 1) → κ` is the maximal ideal. -/
theorem ker_residue (r : ℕ) : RingHom.ker (residue O r) = maximalIdeal (Truncation O r) :=
  (Ideal.Quotient.factor_ker _).trans (maximalIdeal_eq_map O r).symm

/-- An element of `O ⧸ 𝔪 ^ (r + 1)` is a unit if and only if its residue is nonzero. -/
theorem isUnit_iff_residue_ne_zero (r : ℕ) (x : Truncation O r) :
    IsUnit x ↔ residue O r x ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

/-- The residue maps commute with the reductions `O ⧸ 𝔪 ^ (r + 1) → O ⧸ 𝔪 ^ (s + 1)`. -/
@[simp]
theorem residue_factor {s r : ℕ} (hsr : s ≤ r) (x : Truncation O r) :
    residue O s (factor O hsr x) = residue O r x := by
  obtain ⟨y, rfl⟩ := mk_surjective O r x
  rfl

/-- The composite `O ⧸ 𝔪 ^ (r + 1) → O ⧸ 𝔪 ^ (s + 1) → κ` is the residue map. -/
@[simp]
theorem residue_comp_factor {s r : ℕ} (hsr : s ≤ r) :
    (residue O s).comp (factor O hsr) = residue O r :=
  RingHom.ext (residue_factor O hsr)

/-- Reducing the coefficients of `f ∈ O((T))` modulo `𝔪 ^ (r + 1)` and then to `κ` is reducing
them to `κ`. -/
@[simp]
theorem mapRingHom_residue_mapRingHom_mk (r : ℕ) (f : LaurentSeries O) :
    mapRingHom (residue O r) (mapRingHom (mk O r) f) = mapRingHom (IsLocalRing.residue O) f :=
  rfl

/-- Reducing the coefficients of `G ∈ (O ⧸ 𝔪 ^ (r + 1))((T))` modulo `𝔪 ^ (s + 1)` and then to
`κ` is reducing them to `κ`. -/
@[simp]
theorem mapRingHom_residue_mapRingHom_factor {s r : ℕ} (hsr : s ≤ r)
    (G : LaurentSeries (Truncation O r)) :
    mapRingHom (residue O s) (mapRingHom (factor O hsr) G) = mapRingHom (residue O r) G := by
  rw [← RingHom.comp_apply, ← mapRingHom_comp, residue_comp_factor]

/-- The ideal `𝔪 ^ (r + 1) O((T))` is contained in the kernel of reduction modulo
`𝔪 ^ (r + 1)`. -/
theorem adicIdeal_pow_le_ker (r : ℕ) :
    CoefficientRing.adicIdeal O ^ (r + 1) ≤ RingHom.ker (mapRingHom (mk O r)) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, mapRingHom_C, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    map_zero]

/-- Coefficientwise reduction `O((T)) ⧸ 𝔪 ^ (r + 1) O((T)) → (O ⧸ 𝔪 ^ (r + 1))((T))`. -/
def laurentSeriesQuotientMap (r : ℕ) :
    LaurentSeries O ⧸ CoefficientRing.adicIdeal O ^ (r + 1) →+* LaurentSeries (Truncation O r) :=
  Ideal.Quotient.lift _ (mapRingHom (mk O r)) fun _ h ↦ adicIdeal_pow_le_ker O r h

/-- The map `O((T)) ⧸ 𝔪 ^ (r + 1) O((T)) → (O ⧸ 𝔪 ^ (r + 1))((T))` is surjective. -/
theorem laurentSeriesQuotientMap_surjective (r : ℕ) :
    Function.Surjective (laurentSeriesQuotientMap O r) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ (mapRingHom_surjective _ (mk_surjective O r))

/-- The maps `O((T)) ⧸ 𝔪 ^ (r + 1) O((T)) → (O ⧸ 𝔪 ^ (r + 1))((T))` are compatible with the
reductions. -/
theorem mapRingHom_factor_laurentSeriesQuotientMap {s r : ℕ} (hsr : s ≤ r)
    (x : LaurentSeries O ⧸ CoefficientRing.adicIdeal O ^ (r + 1)) :
    mapRingHom (factor O hsr) (laurentSeriesQuotientMap O r x) =
      laurentSeriesQuotientMap O s
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hsr)) x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable [IsPrincipalIdealRing O]

/-- The kernel of coefficientwise reduction `O((T)) → (O ⧸ 𝔪 ^ (r + 1))((T))` is
`𝔪 ^ (r + 1) O((T))`. -/
theorem ker_mapRingHom_mk (r : ℕ) :
    RingHom.ker (mapRingHom (mk O r)) = CoefficientRing.adicIdeal O ^ (r + 1) := by
  rw [LaurentSeries.ker_mapRingHom_mk, Ideal.map_pow]

/-- If `𝔪` is principal, the map `O((T)) ⧸ 𝔪 ^ (r + 1) O((T)) → (O ⧸ 𝔪 ^ (r + 1))((T))` is
injective. -/
theorem laurentSeriesQuotientMap_injective (r : ℕ) :
    Function.Injective (laurentSeriesQuotientMap O r) := by
  intro x y h
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq, ← ker_mapRingHom_mk, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact h

/-- Coefficientwise reduction identifies `O((T)) ⧸ 𝔪 ^ (r + 1) O((T))` with
`(O ⧸ 𝔪 ^ (r + 1))((T))`. -/
def laurentSeriesQuotientEquiv (r : ℕ) :
    LaurentSeries O ⧸ CoefficientRing.adicIdeal O ^ (r + 1) ≃+*
      LaurentSeries (Truncation O r) :=
  .ofBijective (laurentSeriesQuotientMap O r)
    ⟨laurentSeriesQuotientMap_injective O r, laurentSeriesQuotientMap_surjective O r⟩

/-- The isomorphism `O((T)) ⧸ 𝔪 ^ (r + 1) O((T)) ≃ (O ⧸ 𝔪 ^ (r + 1))((T))` is coefficientwise
reduction. -/
@[simp]
theorem laurentSeriesQuotientEquiv_apply (r : ℕ)
    (x : LaurentSeries O ⧸ CoefficientRing.adicIdeal O ^ (r + 1)) :
    laurentSeriesQuotientEquiv O r x = laurentSeriesQuotientMap O r x := rfl

end Truncation

/-- The coefficient ring `A` of Yuan, Definition 1.1 (Berger 2014): the `𝔪`-adic completion of
`O((T))`. For a uniformizer `ϖ` of a discrete valuation ring `O` it is the `ϖ`-adic completion
of `O⟦T⟧[1/T]`. -/
def CoefficientRing : Type _ :=
  AdicCompletion (CoefficientRing.adicIdeal O) (LaurentSeries O)

namespace CoefficientRing

/-- `A` is a commutative ring. -/
instance : CommRing (CoefficientRing O) :=
  inferInstanceAs (CommRing (AdicCompletion (adicIdeal O) (LaurentSeries O)))

/-- `A` is an `O((T))`-algebra. -/
instance : Algebra (LaurentSeries O) (CoefficientRing O) :=
  inferInstanceAs (Algebra (LaurentSeries O) (AdicCompletion (adicIdeal O) (LaurentSeries O)))

/-- `A` is an `O⟦T⟧`-algebra. -/
instance : Algebra (PowerSeries O) (CoefficientRing O) :=
  inferInstanceAs (Algebra (PowerSeries O) (AdicCompletion (adicIdeal O) (LaurentSeries O)))

/-- `A` is an `O`-algebra. -/
instance : Algebra O (CoefficientRing O) :=
  inferInstanceAs (Algebra O (AdicCompletion (adicIdeal O) (LaurentSeries O)))

/-- The map `O⟦T⟧ → A` is `O⟦T⟧ → O((T)) → A`. -/
instance : IsScalarTower (PowerSeries O) (LaurentSeries O) (CoefficientRing O) :=
  inferInstanceAs (IsScalarTower (PowerSeries O) (LaurentSeries O)
    (AdicCompletion (adicIdeal O) (LaurentSeries O)))

/-- The map `O → A` is `O → O((T)) → A`. -/
theorem algebraMap_eq :
    algebraMap O (CoefficientRing O) =
      (algebraMap (LaurentSeries O) (CoefficientRing O)).comp HahnSeries.C := by
  ext b
  change AdicCompletion.of _ _ (algebraMap O (LaurentSeries O) b) =
    AdicCompletion.of _ _ (HahnSeries.C b)
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

/-- The reduction `A → (O ⧸ 𝔪 ^ (r + 1))((T))`. -/
def reduction (r : ℕ) : CoefficientRing O →+* LaurentSeries (Truncation O r) :=
  (Truncation.laurentSeriesQuotientMap O r).comp
    (AdicCompletion.evalₐ (adicIdeal O) (r + 1)).toRingHom

private theorem reduction_apply (r : ℕ) (x : CoefficientRing O) :
    reduction O r x =
      Truncation.laurentSeriesQuotientMap O r (AdicCompletion.evalₐ (adicIdeal O) (r + 1) x) :=
  rfl

/-- The reduction of `f ∈ O((T))` modulo `𝔪 ^ (r + 1)` is the coefficientwise reduction of `f`. -/
@[simp]
theorem reduction_algebraMap_laurentSeries (r : ℕ) (f : LaurentSeries O) :
    reduction O r (algebraMap (LaurentSeries O) (CoefficientRing O) f) =
      mapRingHom (Truncation.mk O r) f := by
  rw [reduction_apply]
  exact congrArg (Truncation.laurentSeriesQuotientMap O r)
    (AdicCompletion.evalₐ_of (adicIdeal O) (r + 1) f)

/-- The reduction of `b ∈ O` modulo `𝔪 ^ (r + 1)` is the constant series `b mod 𝔪 ^ (r + 1)`. -/
@[simp]
theorem reduction_algebraMap (r : ℕ) (b : O) :
    reduction O r (algebraMap O (CoefficientRing O) b) = HahnSeries.C (Truncation.mk O r b) := by
  rw [algebraMap_eq, RingHom.comp_apply, reduction_algebraMap_laurentSeries, mapRingHom_C]

/-- The reduction of `P ∈ O⟦T⟧` modulo `𝔪 ^ (r + 1)` is the coefficientwise reduction of `P`. -/
@[simp]
theorem reduction_algebraMap_powerSeries (r : ℕ) (P : PowerSeries O) :
    reduction O r (algebraMap (PowerSeries O) (CoefficientRing O) P) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (Truncation.mk O r) P) := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries O) (LaurentSeries O),
    reduction_algebraMap_laurentSeries, LaurentSeries.coe_algebraMap, mapRingHom_ofPowerSeries]

/-- The reduction `A → (O ⧸ 𝔪 ^ (r + 1))((T))` is surjective. -/
theorem reduction_surjective (r : ℕ) : Function.Surjective (reduction O r) :=
  (Truncation.laurentSeriesQuotientMap_surjective O r).comp
    (AdicCompletion.surjective_evalₐ _ _)

/-- The reductions of an element of `A` are compatible. -/
@[simp]
theorem mapRingHom_factor_reduction {s r : ℕ} (hsr : s ≤ r) (x : CoefficientRing O) :
    mapRingHom (Truncation.factor O hsr) (reduction O r x) = reduction O s x := by
  rw [reduction_apply, reduction_apply, Truncation.mapRingHom_factor_laurentSeriesQuotientMap]
  exact congrArg (Truncation.laurentSeriesQuotientMap O s)
    (AdicCompletion.factor_evalₐ (adicIdeal O) (Nat.succ_le_succ hsr) x)

/-- The reduction `A → κ((T))` to Laurent series over the residue field `κ` of `O`. -/
def residue : CoefficientRing O →+* LaurentSeries (ResidueField O) :=
  (mapRingHom (Truncation.residue O 0)).comp (reduction O 0)

/-- The reduction `A → κ((T))` factors through every reduction `A → (O ⧸ 𝔪 ^ (r + 1))((T))`. -/
@[simp]
theorem mapRingHom_residue_reduction (r : ℕ) (x : CoefficientRing O) :
    mapRingHom (Truncation.residue O r) (reduction O r x) = residue O x := by
  rw [residue, RingHom.comp_apply, ← mapRingHom_factor_reduction O (Nat.zero_le r),
    Truncation.mapRingHom_residue_mapRingHom_factor]

/-- The image of `f ∈ O((T))` in `κ((T))` is the coefficientwise reduction of `f`. -/
@[simp]
theorem residue_algebraMap_laurentSeries (f : LaurentSeries O) :
    residue O (algebraMap (LaurentSeries O) (CoefficientRing O) f) =
      mapRingHom (IsLocalRing.residue O) f := by
  rw [residue, RingHom.comp_apply, reduction_algebraMap_laurentSeries,
    Truncation.mapRingHom_residue_mapRingHom_mk]

/-- The reduction `A → κ((T))` is surjective. -/
theorem residue_surjective : Function.Surjective (residue O) :=
  (mapRingHom_surjective _ (Truncation.residue_surjective O 0)).comp (reduction_surjective O 0)

variable [IsPrincipalIdealRing O]

/-- If `𝔪` is principal, the ideal `𝔪 O((T))` is finitely generated. -/
theorem adicIdeal_fg : (adicIdeal O).FG :=
  Ideal.FG.map (IsNoetherian.noetherian _) _

/-- The kernel of the reduction `A → (O ⧸ 𝔪 ^ (r + 1))((T))` is `𝔪 ^ (r + 1) A`. -/
theorem ker_reduction (r : ℕ) :
    RingHom.ker (reduction O r) =
      (maximalIdeal O).map (algebraMap O (CoefficientRing O)) ^ (r + 1) := by
  have h := AdicCompletion.ker_evalₐ_eq_map_pow (adicIdeal O) (adicIdeal_fg O) (r + 1)
  rw [Ideal.map_pow, Ideal.map_map] at h
  ext x
  rw [RingHom.mem_ker, reduction_apply,
    map_eq_zero_iff _ (Truncation.laurentSeriesQuotientMap_injective O r), algebraMap_eq]
  exact RingHom.mem_ker.symm.trans (SetLike.ext_iff.mp h x)

/-- An element of `A` is determined by its reductions. -/
theorem ext_reduction {x y : CoefficientRing O} (h : ∀ r, reduction O r x = reduction O r y) :
    x = y := by
  refine AdicCompletion.ext_evalₐ (I := adicIdeal O) fun n ↦ ?_
  cases n with
  | zero =>
    have : Subsingleton (LaurentSeries O ⧸ adicIdeal O ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    exact Subsingleton.elim _ _
  | succ r =>
    apply Truncation.laurentSeriesQuotientMap_injective O r
    simpa only [reduction_apply] using h r

section Lift

variable {O} {B : Type*} [CommRing B] (f : (r : ℕ) → B →+* LaurentSeries (Truncation O r))
  (hf : ∀ {s r : ℕ} (hsr : s ≤ r), (mapRingHom (Truncation.factor O hsr)).comp (f r) = f s)

include hf in
private theorem factor_symm {s r : ℕ} (hsr : s ≤ r) (x : B) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hsr))
      ((Truncation.laurentSeriesQuotientEquiv O r).symm (f r x)) =
      (Truncation.laurentSeriesQuotientEquiv O s).symm (f s x) := by
  apply (Truncation.laurentSeriesQuotientEquiv O s).injective
  rw [RingEquiv.apply_symm_apply, Truncation.laurentSeriesQuotientEquiv_apply,
    ← Truncation.mapRingHom_factor_laurentSeriesQuotientMap,
    ← Truncation.laurentSeriesQuotientEquiv_apply, RingEquiv.apply_symm_apply, ← hf hsr,
    RingHom.comp_apply]

include hf in
private theorem lift_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (adicIdeal O) hmn).comp
      ((Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)).comp
        ((Truncation.laurentSeriesQuotientEquiv O n).symm.toRingHom.comp (f n))) =
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.le_succ)).comp
        ((Truncation.laurentSeriesQuotientEquiv O m).symm.toRingHom.comp (f m)) := by
  ext x : 1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    ← factor_symm f hf hmn x, Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply]

/-- The ring homomorphism `B → A` induced by a family of ring homomorphisms
`f r : B → (O ⧸ 𝔪 ^ (r + 1))((T))` compatible with the reductions. -/
def lift : B →+* CoefficientRing O :=
  AdicCompletion.liftRingHom (adicIdeal O)
    (fun n ↦ (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)).comp
      ((Truncation.laurentSeriesQuotientEquiv O n).symm.toRingHom.comp (f n)))
    (by exact lift_compatible f hf)

/-- The reduction of `lift f hf x` modulo `𝔪 ^ (r + 1)` is `f r x`. -/
@[simp]
theorem reduction_lift (r : ℕ) (x : B) : reduction O r (lift f hf x) = f r x := by
  have h : AdicCompletion.evalₐ (adicIdeal O) (r + 1) (lift f hf x) =
      (Truncation.laurentSeriesQuotientEquiv O r).symm (f r x) :=
    (AdicCompletion.evalₐ_liftRingHom _ _ (lift_compatible f hf) _ _).trans
      (factor_symm f hf r.le_succ x)
  rw [reduction_apply]
  exact (congrArg (Truncation.laurentSeriesQuotientMap O r) h).trans
    ((Truncation.laurentSeriesQuotientEquiv O r).apply_symm_apply (f r x))

end Lift

end CoefficientRing

end FalseTateNonliftability

end Truncations

/-! ### `A` is a complete local ring -/

section LocalRing

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries
open IsLocalRing (maximalIdeal ResidueField)

variable (O : Type*) [CommRing O] [IsLocalRing O] [IsPrincipalIdealRing O]

/-- The kernel of `O((T)) → κ((T))` is `𝔪 O((T))`. -/
theorem ker_mapRingHom_residue :
    RingHom.ker (mapRingHom (IsLocalRing.residue O)) = adicIdeal O :=
  LaurentSeries.ker_mapRingHom_mk (maximalIdeal O)

/-- The ideal `𝔪 O((T))` is maximal, with quotient field `κ((T))`. -/
theorem isMaximal_adicIdeal : (adicIdeal O).IsMaximal :=
  ker_mapRingHom_residue O ▸ RingHom.ker_isMaximal_of_surjective _
    (mapRingHom_surjective _ IsLocalRing.residue_surjective)

private theorem isMaximal_map_adicIdeal :
    ((adicIdeal O).map (algebraMap (LaurentSeries O) (CoefficientRing O))).IsMaximal :=
  have := isMaximal_adicIdeal O
  AdicCompletion.isMaximal_map_of_le (adicIdeal O) (adicIdeal O) le_rfl (adicIdeal_fg O)

private theorem isAdicComplete_map_adicIdeal :
    IsAdicComplete ((adicIdeal O).map (algebraMap (LaurentSeries O) (CoefficientRing O)))
      (CoefficientRing O) :=
  AdicCompletion.isAdicComplete_self (adicIdeal O) (adicIdeal_fg O)

/-- `A` is a local ring (Yuan, Definition 1.1). -/
instance isLocalRing : IsLocalRing (CoefficientRing O) :=
  have := isMaximal_map_adicIdeal O
  have := isAdicComplete_map_adicIdeal O
  isLocalRing_of_isAdicComplete_maximal
    ((adicIdeal O).map (algebraMap (LaurentSeries O) (CoefficientRing O)))

private theorem maximalIdeal_eq_map_adicIdeal :
    maximalIdeal (CoefficientRing O) =
      (adicIdeal O).map (algebraMap (LaurentSeries O) (CoefficientRing O)) :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_map_adicIdeal O)).symm

/-- The maximal ideal of `A` is `𝔪 A`. -/
theorem maximalIdeal_eq_map :
    maximalIdeal (CoefficientRing O) = (maximalIdeal O).map (algebraMap O (CoefficientRing O)) := by
  rw [maximalIdeal_eq_map_adicIdeal, Ideal.map_map, ← algebraMap_eq]

/-- The kernel of `A → (O ⧸ 𝔪 ^ (r + 1))((T))` is the `(r + 1)`-st power of the maximal ideal
of `A`. -/
theorem ker_reduction_eq_maximalIdeal_pow (r : ℕ) :
    RingHom.ker (reduction O r) = maximalIdeal (CoefficientRing O) ^ (r + 1) := by
  rw [ker_reduction, maximalIdeal_eq_map]

omit [IsPrincipalIdealRing O] in
private theorem mapRingHom_residue_zero_injective :
    Function.Injective (mapRingHom (Truncation.residue O 0)) := by
  have h : Function.Injective (Truncation.residue O 0) := by
    rw [RingHom.injective_iff_ker_eq_bot, Truncation.ker_residue, Truncation.maximalIdeal_eq_map,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, zero_add, pow_one]
  intro f g hfg
  ext n
  exact h (congrArg (fun x ↦ HahnSeries.coeff x n) hfg)

/-- The kernel of the reduction `A → κ((T))` is the maximal ideal of `A`. -/
theorem ker_residue : RingHom.ker (residue O) = maximalIdeal (CoefficientRing O) := by
  ext x
  rw [RingHom.mem_ker, residue, RingHom.comp_apply,
    map_eq_zero_iff _ (mapRingHom_residue_zero_injective O), ← RingHom.mem_ker,
    ker_reduction_eq_maximalIdeal_pow, zero_add, pow_one]

/-- `A` is complete and separated for its maximal ideal (Yuan, Definition 1.1). -/
instance isAdicComplete : IsAdicComplete (maximalIdeal (CoefficientRing O)) (CoefficientRing O) :=
  maximalIdeal_eq_map_adicIdeal O ▸ isAdicComplete_map_adicIdeal O

/-- The residue field of `A` is `κ((T))` (Yuan, Definition 1.1). -/
def residueFieldEquiv : ResidueField (CoefficientRing O) ≃+* LaurentSeries (ResidueField O) :=
  (Ideal.quotEquivOfEq (ker_residue O).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residue_surjective O))

/-- The isomorphism of the residue field of `A` with `κ((T))` is induced by the reduction
`A → κ((T))` (Yuan, Definition 1.1). -/
@[simp]
theorem residueFieldEquiv_residue (x : CoefficientRing O) :
    residueFieldEquiv O (IsLocalRing.residue _ x) = residue O x := rfl

end FalseTateNonliftability.CoefficientRing

end LocalRing

/-! ### `A` is a discrete valuation ring -/

section DiscreteValuationRing

namespace FalseTateNonliftability.CoefficientRing

open IsLocalRing (maximalIdeal)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem maximalIdeal_eq_span {ϖ : O} (hϖ : Irreducible ϖ) :
    maximalIdeal (CoefficientRing O) = Ideal.span {algebraMap O (CoefficientRing O) ϖ} := by
  rw [maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

private theorem algebraMap_pow_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    algebraMap O (CoefficientRing O) ϖ ^ n ≠ 0 := by
  intro h
  have h' := congrArg (reduction O n) h
  rw [← map_pow, reduction_algebraMap, map_zero, ← map_zero HahnSeries.C] at h'
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp (HahnSeries.C_injective h')
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hmem
  omega

private theorem exists_eq_pow_mul_unit {ϖ : O} (hϖ : Irreducible ϖ) {x : CoefficientRing O}
    (hx : x ≠ 0) : ∃ (n : ℕ) (u : (CoefficientRing O)ˣ),
      x = algebraMap O (CoefficientRing O) ϖ ^ n * u := by
  set t := algebraMap O (CoefficientRing O) ϖ
  have hmax := maximalIdeal_eq_span hϖ
  obtain ⟨n, hn, hn1⟩ : ∃ n, x ∈ Ideal.span {t ^ n} ∧ x ∉ Ideal.span {t ^ (n + 1)} := by
    by_contra! h
    have hmem (n : ℕ) : x ∈ Ideal.span {t ^ n} := by
      induction n with
      | zero => simp
      | succ n ih => exact h n ih
    refine hx (IsHausdorff.haus (I := maximalIdeal (CoefficientRing O)) inferInstance x
      fun n ↦ ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hmax, Ideal.span_singleton_pow]
    exact hmem n
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hn
  have hy : IsUnit y := by
    by_contra hy
    have hyt : y ∈ Ideal.span {t} := hmax ▸ (IsLocalRing.mem_maximalIdeal y).mpr hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hyt
    exact hn1 (Ideal.mem_span_singleton.mpr ⟨z, by ring⟩)
  exact ⟨n, hy.unit, rfl⟩

/-- If `O` is a discrete valuation ring, then `A` is an integral domain. -/
instance isDomain : IsDomain (CoefficientRing O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : NoZeroDivisors (CoefficientRing O) := ⟨fun {a b} hab ↦ by
    by_contra! h
    obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit hϖ h.1
    obtain ⟨m, v, rfl⟩ := exists_eq_pow_mul_unit hϖ h.2
    have h' : algebraMap O (CoefficientRing O) ϖ ^ (n + m) * ↑(u * v) = 0 := by
      rw [← hab, pow_add, Units.val_mul]
      ring
    exact algebraMap_pow_ne_zero hϖ (n + m) ((u * v).isUnit.mul_left_eq_zero.mp h')⟩
  exact NoZeroDivisors.to_isDomain _

/-- A uniformizer of `O` is a uniformizer of `A` (Yuan, Definition 1.1). -/
theorem irreducible_algebraMap {ϖ : O} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap O (CoefficientRing O) ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using algebraMap_pow_ne_zero hϖ 1) (maximalIdeal_eq_span hϖ)

/-- If `O` is a discrete valuation ring, so is `A` (Yuan, Definition 1.1). -/
instance isDiscreteValuationRing : IsDiscreteValuationRing (CoefficientRing O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine .ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap O (CoefficientRing O) ϖ, irreducible_algebraMap hϖ, fun hx ↦ ?_⟩
  obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit hϖ hx
  exact ⟨n, u, rfl⟩

end FalseTateNonliftability.CoefficientRing

end DiscreteValuationRing

end

end

/-! ### The layers of the truncated coefficient rings -/

section Layers

noncomputable section

namespace FalseTateNonliftability.Truncation

open LaurentSeries
open IsLocalRing (maximalIdeal ResidueField)

@[expose] public section

variable (O : Type*) [CommRing O] [IsLocalRing O]

/-- The ideal `𝔪 ^ j R_r` of `R_r = (O ⧸ 𝔪 ^ (r + 1))((T))` generated by `𝔪 ^ j`; for a
uniformizer `ϖ` of a discrete valuation ring `O` it is `ϖ ^ j R_r`. -/
def layerIdeal (r j : ℕ) : Ideal (LaurentSeries (Truncation O r)) :=
  (maximalIdeal (Truncation O r) ^ j).map
    (HahnSeries.C : Truncation O r →+* LaurentSeries (Truncation O r))

/-- A constant in `𝔪 ^ j` lies in `𝔪 ^ j R_r`. -/
theorem C_mem_layerIdeal {r j : ℕ} {x : Truncation O r}
    (hx : x ∈ maximalIdeal (Truncation O r) ^ j) : HahnSeries.C x ∈ layerIdeal O r j :=
  Ideal.mem_map_of_mem _ hx

/-- The ideals `𝔪 ^ j R_r` decrease with `j`. -/
theorem layerIdeal_antitone (r : ℕ) {i j : ℕ} (hij : i ≤ j) :
    layerIdeal O r j ≤ layerIdeal O r i :=
  Ideal.map_mono (Ideal.pow_le_pow_right hij)

/-- `𝔪 ^ 0 R_r = R_r`. -/
@[simp]
theorem layerIdeal_zero (r : ℕ) : layerIdeal O r 0 = ⊤ := by
  rw [layerIdeal, pow_zero, Ideal.one_eq_top, Ideal.map_top]

/-- `𝔪 ^ j R_r = 0` for `j > r`. -/
theorem layerIdeal_eq_bot {r j : ℕ} (hj : r < j) : layerIdeal O r j = ⊥ := by
  rw [layerIdeal, le_bot_iff.mp ((Ideal.pow_le_pow_right hj).trans
    (maximalIdeal_pow_eq_bot O r).le), Ideal.map_bot]

omit [IsLocalRing O] in
private theorem smul_eq_C_mul {S : Type*} [CommRing S] [Algebra O S] (b : O)
    (X : LaurentSeries S) : b • X = HahnSeries.C (algebraMap O S b) * X := by
  rw [HahnSeries.C_mul_eq_smul, algebraMap_smul]

private theorem algHom_C {r : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (a : Truncation O r) : E (HahnSeries.C a) = HahnSeries.C a := by
  simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C] using E.commutes a

/-- Every `O ⧸ 𝔪 ^ (r + 1)`-algebra endomorphism of `R_r` preserves `𝔪 ^ j R_r`. -/
theorem algHom_mem_layerIdeal {r j : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    E X ∈ layerIdeal O r j := by
  have hE : (E : LaurentSeries (Truncation O r) →+* LaurentSeries (Truncation O r)).comp
      HahnSeries.C = HahnSeries.C := RingHom.ext (algHom_C O E)
  have h := Ideal.mem_map_of_mem
    (E : LaurentSeries (Truncation O r) →+* LaurentSeries (Truncation O r)) hX
  rwa [layerIdeal, Ideal.map_map, hE] at h

/-- An `O ⧸ 𝔪 ^ (r + 1)`-algebra automorphism `E` of `R_r` satisfies `E X ∈ 𝔪 ^ j R_r` if and
only if `X ∈ 𝔪 ^ j R_r`. -/
theorem algEquiv_mem_layerIdeal_iff {r j : ℕ}
    (E : LaurentSeries (Truncation O r) ≃ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (X : LaurentSeries (Truncation O r)) :
    E X ∈ layerIdeal O r j ↔ X ∈ layerIdeal O r j :=
  ⟨fun h ↦ by simpa using algHom_mem_layerIdeal O E.symm.toAlgHom h,
    fun h ↦ algHom_mem_layerIdeal O E.toAlgHom h⟩

/-- The ideal `𝔪 ^ j R_r` as an `O`-submodule of `R_r`. -/
def layerSubmodule (r j : ℕ) : Submodule O (LaurentSeries (Truncation O r)) where
  carrier := layerIdeal O r j
  add_mem' := Ideal.add_mem _
  zero_mem' := Ideal.zero_mem _
  smul_mem' b X hX := by
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ hX

/-- `𝔪 ^ (j + 1) R_r` as an `O`-submodule of `𝔪 ^ j R_r`. -/
def nextLayerSubmodule (r j : ℕ) : Submodule O (layerSubmodule O r j) :=
  (layerSubmodule O r (j + 1)).comap (layerSubmodule O r j).subtype

/-- The graded piece `𝔪 ^ j R_r ⧸ 𝔪 ^ (j + 1) R_r`, an `O`-module. -/
abbrev GradedLayer (r j : ℕ) : Type _ := layerSubmodule O r j ⧸ nextLayerSubmodule O r j

variable [IsPrincipalIdealRing O]

/-- If `𝔪` is principal, `𝔪 ^ j R_r` consists of the Laurent series with coefficients in
`𝔪 ^ j`. -/
theorem mem_layerIdeal_iff {r j : ℕ} (X : LaurentSeries (Truncation O r)) :
    X ∈ layerIdeal O r j ↔ ∀ n, X.coeff n ∈ maximalIdeal (Truncation O r) ^ j :=
  mem_map_C_iff _ X

/-- `𝔪 R_r` is the kernel of the reduction `R_r → κ((T))`. -/
theorem mem_layerIdeal_one_iff {r : ℕ} (X : LaurentSeries (Truncation O r)) :
    X ∈ layerIdeal O r 1 ↔ mapRingHom (residue O r) X = 0 := by
  rw [mem_layerIdeal_iff, pow_one, HahnSeries.ext_iff, funext_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero, ← RingHom.mem_ker, ker_residue]

/-- If `κ` has characteristic `p` and `P ∈ R_r` reduces to `T ^ p`, then `P' ∈ 𝔪 R_r`. -/
theorem derivative_mem_layerIdeal_one (p : ℕ) [CharP (ResidueField O) p] {r : ℕ}
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1) :
    derivative (Truncation O r) P ∈ layerIdeal O r 1 := by
  rw [mem_layerIdeal_one_iff, mapRingHom_derivative, hP, derivative_single, Int.cast_natCast,
    CharP.cast_eq_zero (ResidueField O) p, zero_mul, map_zero]

end

section Uniformizer

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The uniformizer `ϖ` of `O` used to define `Λ_j`. -/
private def uniformizer : O := Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

private theorem irreducible_uniformizer : Irreducible (uniformizer O) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)

private theorem maximalIdeal_pow_eq_span (r j : ℕ) :
    maximalIdeal (Truncation O r) ^ j = Ideal.span {mk O r (uniformizer O) ^ j} := by
  rw [maximalIdeal_eq_map,
    congrArg (Ideal.map (mk O r)) (irreducible_uniformizer O).maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]

private theorem layerIdeal_eq_span (r j : ℕ) :
    layerIdeal O r j = Ideal.span {HahnSeries.C (mk O r (uniformizer O) ^ j)} := by
  rw [layerIdeal, maximalIdeal_pow_eq_span, Ideal.map_span, Set.image_singleton]

private theorem C_mul_mem_layerIdeal (r j : ℕ) (Y : LaurentSeries (Truncation O r)) :
    HahnSeries.C (mk O r (uniformizer O) ^ j) * Y ∈ layerIdeal O r j := by
  rw [layerIdeal_eq_span]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

private theorem exists_eq_C_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) :
    ∃ Y, X = HahnSeries.C (mk O r (uniformizer O) ^ j) * Y := by
  rw [layerIdeal_eq_span] at hX
  exact Ideal.mem_span_singleton.mp hX

private theorem pow_mul_mem_iff {r j : ℕ} (hj : j ≤ r) (y : Truncation O r) :
    mk O r (uniformizer O) ^ j * y ∈ maximalIdeal (Truncation O r) ^ (j + 1) ↔
      residue O r y = 0 := by
  obtain ⟨a, rfl⟩ := mk_surjective O r y
  rw [← map_pow, ← map_mul, mk_mem_maximalIdeal_pow_iff O (by omega), residue_mk,
    IsLocalRing.residue_eq_zero_iff, (irreducible_uniformizer O).maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero j (irreducible_uniformizer O).ne_zero)]

private theorem coeff_C_mul {R : Type*} [CommRing R] (a : R) (Y : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C a * Y).coeff n = a * Y.coeff n := by
  simp

private theorem eq_zero_of_lt {r j : ℕ} (hj : r < j) {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : X = 0 := by
  rwa [layerIdeal_eq_bot O hj, Ideal.mem_bot] at hX

/-- Coefficientwise reduction `O((T)) → κ((T))`, as a map of `O`-modules. -/
private def residueLinear : LaurentSeries O →ₗ[O] LaurentSeries (ResidueField O) where
  __ := (mapRingHom (IsLocalRing.residue O)).toAddMonoidHom
  map_smul' b f := by
    change mapRingHom (IsLocalRing.residue O) (b • f) = b • mapRingHom (IsLocalRing.residue O) f
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, mapRingHom_C, Algebra.algebraMap_self,
      RingHom.id_apply, IsLocalRing.ResidueField.algebraMap_eq]

private theorem residueLinear_apply (f : LaurentSeries O) :
    residueLinear O f = mapRingHom (IsLocalRing.residue O) f := rfl

private theorem residueLinear_surjective : Function.Surjective (residueLinear O) :=
  mapRingHom_surjective _ IsLocalRing.residue_surjective

private theorem mem_ker_residueLinear (f : LaurentSeries O) :
    f ∈ LinearMap.ker (residueLinear O) ↔ ∀ n, IsLocalRing.residue O (f.coeff n) = 0 := by
  rw [LinearMap.mem_ker, residueLinear_apply, HahnSeries.ext_iff, funext_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero]

/-- The map `O((T)) → ϖ ^ j R_r ⧸ ϖ ^ (j + 1) R_r`, `f ↦ ϖ ^ j f mod ϖ ^ (j + 1) R_r`. Its kernel is
the kernel of `O((T)) → κ((T))` for `j ≤ r`, so it induces `Λ_j`. -/
private def gradedLift (r j : ℕ) : LaurentSeries O →ₗ[O] GradedLayer O r j where
  toFun f := Submodule.Quotient.mk
    ⟨HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f,
      C_mul_mem_layerIdeal O r j _⟩
  map_add' f g := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (by simp only [map_add, mul_add, Submodule.coe_add])
  map_smul' b f := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    simp only [SetLike.val_smul, smul_eq_C_mul, map_mul, mapRingHom_C, Algebra.algebraMap_self,
      RingHom.id_apply, Ideal.Quotient.algebraMap_eq]
    ring

private theorem gradedLift_apply (r j : ℕ) (f : LaurentSeries O) :
    gradedLift O r j f = Submodule.Quotient.mk
      ⟨HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f,
        C_mul_mem_layerIdeal O r j _⟩ := rfl

private theorem gradedLift_surjective (r j : ℕ) : Function.Surjective (gradedLift O r j) := by
  intro x
  obtain ⟨⟨X, hX⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
  obtain ⟨f, rfl⟩ := mapRingHom_surjective _ (mk_surjective O r) Y
  exact ⟨f, rfl⟩

private theorem mem_ker_gradedLift {r j : ℕ} (hj : j ≤ r) (f : LaurentSeries O) :
    f ∈ LinearMap.ker (gradedLift O r j) ↔ ∀ n, IsLocalRing.residue O (f.coeff n) = 0 := by
  rw [LinearMap.mem_ker, gradedLift_apply, Submodule.Quotient.mk_eq_zero]
  change HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f ∈
    layerIdeal O r (j + 1) ↔ _
  simp only [mem_layerIdeal_iff, coeff_C_mul, mapRingHom_coeff, pow_mul_mem_iff O hj,
    residue_mk]

private theorem ker_residueLinear_eq {r j : ℕ} (hj : j ≤ r) :
    LinearMap.ker (residueLinear O) = LinearMap.ker (gradedLift O r j) := by
  ext f
  rw [mem_ker_residueLinear, mem_ker_gradedLift O hj]

end Uniformizer

public section

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Yuan, §2.2: for `j ≤ r`, the isomorphism of `O`-modules
`Λ_j : κ((T)) ≃ ϖ ^ j R_r ⧸ ϖ ^ (j + 1) R_r` induced by multiplication by `ϖ ^ j`, for a
uniformizer `ϖ` of `O` chosen once for all `r` and `j`. -/
def gradedLayerEquiv (r j : ℕ) (hj : j ≤ r) :
    LaurentSeries (ResidueField O) ≃ₗ[O] GradedLayer O r j :=
  ((residueLinear O).quotKerEquivOfSurjective (residueLinear_surjective O)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_residueLinear_eq O hj)).trans
      ((gradedLift O r j).quotKerEquivOfSurjective (gradedLift_surjective O r j)))

end

private theorem gradedLayerEquiv_residueLinear (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {r j : ℕ} (hj : j ≤ r) (f : LaurentSeries O) :
    gradedLayerEquiv O r j hj (residueLinear O f) = gradedLift O r j f := by
  simp only [gradedLayerEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

@[expose] public section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open Classical in
/-- Yuan, §2.2: for `j ≤ r` and `X ∈ ϖ ^ j R_r`, the series `ϖ⁻ʲ X ∈ κ((T))`, the preimage of
`X mod ϖ ^ (j + 1) R_r` under `Λ_j`. It is `0` if `X ∉ ϖ ^ j R_r` or `r < j`. -/
def layer {r : ℕ} (j : ℕ) (X : LaurentSeries (Truncation O r)) : LaurentSeries (ResidueField O) :=
  if h : j ≤ r ∧ X ∈ layerIdeal O r j then
    (gradedLayerEquiv O r j h.1).symm (Submodule.Quotient.mk ⟨X, h.2⟩)
  else 0

/-- For `j ≤ r` and `X ∈ ϖ ^ j R_r`, `Λ_j⁻¹ (X mod ϖ ^ (j + 1) R_r) = ϖ⁻ʲ X`. -/
theorem gradedLayerEquiv_symm_mk {r j : ℕ} (hj : j ≤ r) {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) :
    (gradedLayerEquiv O r j hj).symm (Submodule.Quotient.mk ⟨X, hX⟩) = layer j X := by
  rw [layer, dite_eq_left ⟨hj, hX⟩]

/-- `ϖ⁻ʲ X = 0` for `j > r`. -/
theorem layer_of_lt {r j : ℕ} (hj : r < j) (X : LaurentSeries (Truncation O r)) :
    layer j X = 0 := by
  rw [layer, dite_eq_right fun h ↦ by omega]

/-- `ϖ⁻ʲ 0 = 0`. -/
@[simp]
theorem layer_zero {r : ℕ} (j : ℕ) : layer j (0 : LaurentSeries (Truncation O r)) = 0 := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj (Ideal.zero_mem _)]
    exact (LinearEquiv.map_eq_zero_iff _).mpr rfl
  · exact layer_of_lt hj 0

end

private theorem layer_C_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {r j : ℕ} (hj : j ≤ r) (Y : LaurentSeries (Truncation O r)) :
    layer j (HahnSeries.C (mk O r (uniformizer O) ^ j) * Y) = mapRingHom (residue O r) Y := by
  rw [← gradedLayerEquiv_symm_mk hj (C_mul_mem_layerIdeal O r j Y)]
  apply (gradedLayerEquiv O r j hj).injective
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨f, rfl⟩ := mapRingHom_surjective _ (mk_surjective O r) Y
  rw [mapRingHom_residue_mapRingHom_mk, ← residueLinear_apply, gradedLayerEquiv_residueLinear,
    gradedLift_apply]

@[expose] public section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- For `X ∈ ϖ ^ j R_r`, `ϖ⁻ʲ X = 0` if and only if `X ∈ ϖ ^ (j + 1) R_r`. -/
theorem layer_eq_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : layer j X = 0 ↔ X ∈ layerIdeal O r (j + 1) := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj hX, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero]
    rfl
  · obtain rfl := eq_zero_of_lt O hj hX
    simp only [layer_zero, Submodule.zero_mem]

/-- For `X ∈ ϖ ^ j R_r`, `ϖ⁻ʲ X ≠ 0` if and only if `X ∉ ϖ ^ (j + 1) R_r`. -/
theorem layer_ne_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : layer j X ≠ 0 ↔ X ∉ layerIdeal O r (j + 1) :=
  (layer_eq_zero_iff hX).not

/-- For `X ∈ ϖ ^ j R_r`, $\varpi^{-j}(XZ) = \varpi^{-j}X \cdot \bar{Z}$, where $\bar{Z}$ is the
reduction of `Z` to `κ((T))`. -/
theorem layer_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j)
    (Z : LaurentSeries (Truncation O r)) :
    layer j (X * Z) = layer j X * mapRingHom (residue O r) Z := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [mul_assoc, layer_C_mul hj, layer_C_mul hj, map_mul]
  · rw [layer_of_lt hj, layer_of_lt hj, zero_mul]

/-- For `X ∈ ϖ ^ j R_r`, the `n`-th coefficient of `ϖ⁻ʲ X` vanishes if and only if the `n`-th
coefficient of `X` lies in `𝔪 ^ (j + 1)`. -/
theorem coeff_layer_eq_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) (n : ℤ) :
    (layer j X).coeff n = 0 ↔ X.coeff n ∈ maximalIdeal (Truncation O r) ^ (j + 1) := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [layer_C_mul hj, mapRingHom_coeff, coeff_C_mul, pow_mul_mem_iff O hj]
  · obtain rfl := eq_zero_of_lt O hj hX
    simp only [layer_zero, HahnSeries.coeff_zero, Submodule.zero_mem]

/-- If `X ∈ ϖ ^ j R_r` and the `n`-th coefficient of `X` is `a b` with `a ∈ 𝔪 ^ j`, then the
`n`-th coefficient of `ϖ⁻ʲ X` is $\varpi^{-j}a \cdot \bar{b}$, where $\bar{b}$ is the residue of
`b`. -/
theorem coeff_layer_eq_of_coeff_eq_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) {n : ℤ} {a b : Truncation O r}
    (ha : a ∈ maximalIdeal (Truncation O r) ^ j) (h : X.coeff n = a * b) :
    (layer j X).coeff n = (layer j (HahnSeries.C a)).coeff 0 * residue O r b := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [maximalIdeal_pow_eq_span] at ha
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [coeff_C_mul, mul_assoc] at h
    rw [map_mul, layer_C_mul hj, layer_C_mul hj, mapRingHom_coeff, mapRingHom_C,
      HahnSeries.C_apply, HahnSeries.coeff_single_same, ← map_mul]
    have hmem := (pow_mul_mem_iff O hj (Y.coeff n - a' * b)).mp
      (by rw [mul_sub, h, sub_self]; exact zero_mem _)
    rwa [map_sub, sub_eq_zero] at hmem
  · rw [layer_of_lt hj, layer_of_lt hj, HahnSeries.coeff_zero, HahnSeries.coeff_zero, zero_mul]

/-- If an algebra endomorphism `E` of `R_r` reduces to the endomorphism `E'` of `κ((T))`, then
`ϖ⁻ʲ (E X) = E' (ϖ⁻ʲ X)` for `X ∈ ϖ ^ j R_r`. -/
theorem layer_algHom {r j : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (E' : LaurentSeries (ResidueField O) →ₐ[ResidueField O] LaurentSeries (ResidueField O))
    (hE : ∀ Y, mapRingHom (residue O r) (E Y) = E' (mapRingHom (residue O r) Y))
    {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    layer j (E X) = E' (layer j X) := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [map_mul, algHom_C, layer_C_mul hj, layer_C_mul hj, hE]
  · rw [layer_of_lt hj, layer_of_lt hj, map_zero]

end

end FalseTateNonliftability.Truncation

end

end Layers
