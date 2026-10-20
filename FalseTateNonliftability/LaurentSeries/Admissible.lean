/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.CoefficientMap
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Actual Laurent evaluation data from coefficient reduction

Removing the finite prefix below the reduced order produces the unit part
of an actual nilpotent perturbation. The exact principal reduction kernel
supplies its remaining Laurent factor. No division of coefficients or
assumed decomposition is needed.

This proves blueprint lemma `nl:admissible-laurent-decomposition`.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- Removing the prefix below `a` leaves no coefficients below `a`. -/
theorem sub_truncLT_mem_orderAddSubgroup (G : LaurentSeries R) (a : ℤ) :
    G - HahnSeries.truncLT a G ∈ orderAddSubgroup a := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_truncLT_of_lt hj, sub_self]

/-- The finite prefix below a lower bound on reduced order is in the actual
kernel of principal coefficient reduction. -/
theorem principalReduction_truncLT_eq_zero (δ : R) (G : LaurentSeries R) (a : ℤ)
    (horder : (a : WithTop ℤ) ≤ (principalReduction δ G).orderTop) :
    principalReduction δ (HahnSeries.truncLT a G) = 0 := by
  ext j
  simp only [principalReduction_coeff, HahnSeries.coeff_zero]
  by_cases hj : j < a
  · rw [HahnSeries.coeff_truncLT_of_lt hj]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hj).trans_le horder)
  · rw [HahnSeries.coeff_truncLT_of_le (le_of_not_gt hj), map_zero]

private theorem orderTop_sub_truncLT_of_reduction_order
    (δ : R) (G : LaurentSeries R) (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ)) :
    (G - HahnSeries.truncLT a G).orderTop = (a : WithTop ℤ) := by
  have hG : G.coeff a ≠ 0 := by
    intro hzero
    have hred := HahnSeries.coeff_orderTop_ne horder
    apply hred
    simp only [principalReduction_coeff, hzero, map_zero]
  have htail : (G - HahnSeries.truncLT a G).coeff a ≠ 0 := by
    simpa only [HahnSeries.coeff_sub, HahnSeries.coeff_truncLT_of_le le_rfl, sub_zero] using hG
  exact le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero htail)
    (sub_truncLT_mem_orderAddSubgroup G a)

/-- Units lift through the nilpotent coefficient ideal, making the actual
tail a Laurent unit whenever its reduced leading coefficient is a unit. -/
theorem isUnit_sub_truncLT_of_isUnit_reduction_coeff
    (δ : R) (G : LaurentSeries R) (hδ : IsNilpotent δ) (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ))
    (hunit : IsUnit ((principalReduction δ G).coeff a)) :
    IsUnit (G - HahnSeries.truncLT a G) := by
  have hI : IsNilpotent (Ideal.span ({δ} : Set R)) := by
    obtain ⟨r, hr⟩ := hδ
    refine ⟨r, ?_⟩
    change Ideal.span ({δ} : Set R) ^ r = ⊥
    rw [Ideal.span_singleton_pow, hr, Ideal.span_singleton_zero]
  have hcoeff : IsUnit (G.coeff a) := hI.isUnit_quotient_mk_iff.mp hunit
  have htailorder := orderTop_sub_truncLT_of_reduction_order δ G a horder
  have htailne : G - HahnSeries.truncLT a G ≠ 0 := by
    apply HahnSeries.orderTop_ne_top.mp
    rw [htailorder]
    exact WithTop.coe_ne_top
  have htailorder' : (G - HahnSeries.truncLT a G).order = a := by
    exact WithTop.coe_inj.mp
      ((HahnSeries.order_eq_orderTop_of_ne_zero htailne).trans htailorder)
  have hlead : IsUnit (G - HahnSeries.truncLT a G).leadingCoeff := by
    simpa only [HahnSeries.leadingCoeff_eq, htailorder', HahnSeries.coeff_sub,
      HahnSeries.coeff_truncLT_of_le le_rfl, sub_zero] using hcoeff
  exact HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder hlead (AddGroup.isAddUnit _)

/-- A finite reduced order over a maximal nilpotent coefficient ideal supplies
actual Laurent evaluation data, with the unit part equal to the canonical tail.
For positive `a` and `r ≥ 1`, these witnesses have exactly the support and unit
hypotheses required by `nilpotentLaurentEval`, using the same exponent `r`. -/
theorem exists_nilpotentLaurentEval_data
    (δ : R) (G : LaurentSeries R) (r : ℕ) (hδ : δ ^ r = 0)
    [(Ideal.span ({δ} : Set R)).IsMaximal] (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ)) :
    ∃ U Y : LaurentSeries R, ∃ c : ℤ,
      U = G - HahnSeries.truncLT a G ∧
      G = U + HahnSeries.C δ * Y ∧
      U.orderTop = (a : WithTop ℤ) ∧ IsUnit U ∧
      0 ≤ c ∧ ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop := by
  let := Ideal.Quotient.field (Ideal.span ({δ} : Set R))
  have hprefix : HahnSeries.truncLT a G ∈ Ideal.span {HahnSeries.C δ} := by
    rw [← ker_principalReduction, RingHom.mem_ker]
    exact principalReduction_truncLT_eq_zero δ G a horder.ge
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hprefix
  have htailunit : IsUnit (G - HahnSeries.truncLT a G) :=
    isUnit_sub_truncLT_of_isUnit_reduction_coeff δ G ⟨r, hδ⟩ a horder
      (isUnit_iff_ne_zero.mpr (HahnSeries.coeff_orderTop_ne horder))
  refine ⟨G - HahnSeries.truncLT a G, Y, max (-Y.order) 0, rfl, ?_,
    orderTop_sub_truncLT_of_reduction_order δ G a horder, htailunit, le_max_right _ _, ?_⟩
  · rw [← hY]
    exact (sub_add_cancel G (HahnSeries.truncLT a G)).symm
  · exact (WithTop.coe_le_coe.mpr (show -max (-Y.order) 0 ≤ Y.order by omega)).trans
      (mem_orderAddSubgroup_order Y)

end

end LaurentSeries
