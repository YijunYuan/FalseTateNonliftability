/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.CharacteristicP

/-!
# Normalizing Laurent primitives in characteristic p

Deleting the terms whose exponents are divisible by the characteristic preserves
the derivative. If the derivative is nonzero, the resulting primitive has order
one larger than its derivative and order prime to the characteristic.
This is the normalization clause of `nl:characteristic-p-differentiation`.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {F : Type*} [Field F]

local instance : DecidableEq F := Classical.decEq F

/-- Normalizing a primitive deletes exactly the exponents whose integer image
vanishes in the coefficient field. -/
theorem coefficientPrimitive_derivative_coeff (U : LaurentSeries F) (n : ℤ) :
    (coefficientPrimitive (derivative F U)).coeff n =
      if (n : F) = 0 then 0 else U.coeff n := by
  rw [coefficientPrimitive_coeff, derivative_coeff]
  simp only [sub_add_cancel]
  by_cases hn : (n : F) = 0 <;> simp [hn]

/-- In characteristic `p`, normalization deletes exactly the terms with
exponent divisible by `p`, retaining every other coefficient. -/
theorem coefficientPrimitive_derivative_coeff_charP (p : ℕ) [CharP F p]
    (U : LaurentSeries F) (n : ℤ) :
    (coefficientPrimitive (derivative F U)).coeff n =
      if (p : ℤ) ∣ n then 0 else U.coeff n := by
  simp only [coefficientPrimitive_derivative_coeff, CharP.intCast_eq_zero_iff F p n]

/-- Deleting the terms killed by differentiation preserves the derivative. -/
theorem derivative_coefficientPrimitive_derivative (U : LaurentSeries F) :
    derivative F (coefficientPrimitive (derivative F U)) = derivative F U := by
  ext n
  rw [derivative_coeff, coefficientPrimitive_derivative_coeff, derivative_coeff]
  by_cases hn : ((n + 1 : ℤ) : F) = 0
  · rw [ite_eq_left hn, hn]
    simp
  · rw [ite_eq_right hn]

/-- A nonzero Laurent derivative has normalized primitive of order one larger
than the derivative. The nonvanishing hypothesis is essential because the
canonical Hahn-series order of zero is zero. -/
theorem order_coefficientPrimitive_derivative (U : LaurentSeries F)
    (hU : derivative F U ≠ 0) :
    (coefficientPrimitive (derivative F U)).order = (derivative F U).order + 1 := by
  have hc : (derivative F U).coeff (derivative F U).order ≠ 0 := by
    exact fun hz ↦ hU (HahnSeries.coeff_order_eq_zero.mp hz)
  have hn : (((derivative F U).order + 1 : ℤ) : F) ≠ 0 := by
    intro hz
    apply hc
    rw [derivative_coeff, hz, zero_mul]
  have hcp : (coefficientPrimitive (derivative F U)).coeff
      ((derivative F U).order + 1) ≠ 0 := by
    rw [coefficientPrimitive_coeff, add_sub_cancel_right]
    exact div_ne_zero hc hn
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcp)
  apply (HahnSeries.le_order_iff_forall (HahnSeries.ne_zero_of_coeff_ne_zero hcp)).mpr
  intro j hj
  rw [coefficientPrimitive_coeff,
    HahnSeries.coeff_eq_zero_of_lt_order (by omega : j - 1 < (derivative F U).order),
    zero_div]

/-- The lowest exponent of a normalized primitive of a nonzero derivative is
not divisible by the characteristic. -/
theorem not_dvd_order_coefficientPrimitive_derivative (p : ℕ) [CharP F p]
    (U : LaurentSeries F) (hU : derivative F U ≠ 0) :
    ¬ (p : ℤ) ∣ (coefficientPrimitive (derivative F U)).order := by
  intro hd
  have hP : coefficientPrimitive (derivative F U) ≠ 0 := by
    intro hzero
    apply hU
    rw [← derivative_coefficientPrimitive_derivative U, hzero, map_zero]
  apply hP
  apply HahnSeries.coeff_order_eq_zero.mp
  rw [coefficientPrimitive_derivative_coeff_charP p, ite_eq_left hd]

end

end LaurentSeries
