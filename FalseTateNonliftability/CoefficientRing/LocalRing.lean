/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# The coefficient ring `A` is a complete local ring

Let `O` be a local ring with principal maximal ideal `𝔪` and residue field `κ`, for instance a
discrete valuation ring. The coefficient ring `A`, the `𝔪`-adic completion of `O((T))`, is a local
ring with maximal ideal `𝔪 A`; it is complete for its maximal ideal, and the reduction
`A → κ((T))` identifies its residue field with `κ((T))`. This is part of the statement of
Yuan, Definition 1.1; the proofs of the main results do not use it.

## Main results

* `CoefficientRing.isLocalRing`: `A` is a local ring.
* `CoefficientRing.maximalIdeal_eq_map`: the maximal ideal of `A` is `𝔪 A`.
* `CoefficientRing.ker_reduction_eq_maximalIdeal_pow`: the kernel of
  `A → (O ⧸ 𝔪 ^ (r + 1))((T))` is the `(r + 1)`-st power of the maximal ideal of `A`.
* `CoefficientRing.isAdicComplete`: `A` is complete for its maximal ideal.
* `CoefficientRing.residueFieldEquiv`: the residue field of `A` is `κ((T))`.

## References

* Yuan, Definition 1.1.
-/

@[expose] public section

noncomputable section

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

instance isAdicComplete : IsAdicComplete (maximalIdeal (CoefficientRing O)) (CoefficientRing O) :=
  maximalIdeal_eq_map_adicIdeal O ▸ isAdicComplete_map_adicIdeal O

/-- The residue field of `A` is `κ((T))`. -/
def residueFieldEquiv : ResidueField (CoefficientRing O) ≃+* LaurentSeries (ResidueField O) :=
  (Ideal.quotEquivOfEq (ker_residue O).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residue_surjective O))

@[simp]
theorem residueFieldEquiv_residue (x : CoefficientRing O) :
    residueFieldEquiv O (IsLocalRing.residue _ x) = residue O x := rfl

end FalseTateNonliftability.CoefficientRing
