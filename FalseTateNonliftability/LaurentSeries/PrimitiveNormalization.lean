/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.CharacteristicP

/-!
# Normalized primitives of Laurent series in characteristic `p`

Let `κ` be a field of characteristic `p` and `U ∈ κ((T))`. Deleting from `U` the terms whose
exponents are divisible by `p` gives the primitive `coefficientPrimitive U'` of `U'`. If `U' ≠ 0`,
this primitive has order `v_T(U') + 1`, which is not divisible by `p`.

## Main results

* `LaurentSeries.derivative_coefficientPrimitive_derivative`: `(coefficientPrimitive U')' = U'`.
* `LaurentSeries.order_coefficientPrimitive_derivative`:
  `v_T(coefficientPrimitive U') = v_T(U') + 1` for `U' ≠ 0`.
* `LaurentSeries.not_dvd_order_coefficientPrimitive_derivative`:
  `p ∤ v_T(coefficientPrimitive U')` for `U' ≠ 0`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Proposition 4.3.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {κ : Type*} [Field κ]

/-- `coefficientPrimitive U'` is obtained from `U` by deleting the terms in the degrees `n` with
`(n : κ) = 0`. -/
theorem coefficientPrimitive_derivative_coeff [DecidableEq κ] (U : LaurentSeries κ) (n : ℤ) :
    (coefficientPrimitive (derivative κ U)).coeff n =
      if (n : κ) = 0 then 0 else U.coeff n := by
  rw [coefficientPrimitive_coeff, derivative_coeff]
  simp only [sub_add_cancel]
  by_cases hn : (n : κ) = 0 <;> simp [hn]

/-- In characteristic `p`, `coefficientPrimitive U'` is obtained from `U` by deleting the terms
whose exponents are divisible by `p`. -/
theorem coefficientPrimitive_derivative_coeff_charP (p : ℕ) [CharP κ p]
    (U : LaurentSeries κ) (n : ℤ) :
    (coefficientPrimitive (derivative κ U)).coeff n =
      if (p : ℤ) ∣ n then 0 else U.coeff n := by
  classical
  simp only [coefficientPrimitive_derivative_coeff, CharP.intCast_eq_zero_iff κ p n]

/-- `coefficientPrimitive U'` is a primitive of `U'`. -/
theorem derivative_coefficientPrimitive_derivative (U : LaurentSeries κ) :
    derivative κ (coefficientPrimitive (derivative κ U)) = derivative κ U := by
  classical
  ext n
  rw [derivative_coeff, coefficientPrimitive_derivative_coeff, derivative_coeff]
  by_cases hn : ((n + 1 : ℤ) : κ) = 0
  · rw [ite_eq_left hn, hn]
    simp
  · rw [ite_eq_right hn]

/-- If `U' ≠ 0`, then `v_T(coefficientPrimitive U') = v_T(U') + 1`. -/
theorem order_coefficientPrimitive_derivative (U : LaurentSeries κ)
    (hU : derivative κ U ≠ 0) :
    (coefficientPrimitive (derivative κ U)).order = (derivative κ U).order + 1 := by
  have hc : (derivative κ U).coeff (derivative κ U).order ≠ 0 :=
    fun hz ↦ hU (HahnSeries.coeff_order_eq_zero.mp hz)
  have hn : (((derivative κ U).order + 1 : ℤ) : κ) ≠ 0 := by
    intro hz
    apply hc
    rw [derivative_coeff, hz, zero_mul]
  have hcp : (coefficientPrimitive (derivative κ U)).coeff
      ((derivative κ U).order + 1) ≠ 0 := by
    rw [coefficientPrimitive_coeff, add_sub_cancel_right]
    exact div_ne_zero hc hn
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcp)
  apply (HahnSeries.le_order_iff_forall (HahnSeries.ne_zero_of_coeff_ne_zero hcp)).mpr
  intro j hj
  rw [coefficientPrimitive_coeff,
    HahnSeries.coeff_eq_zero_of_lt_order (by omega : j - 1 < (derivative κ U).order),
    zero_div]

/-- In characteristic `p`, if `U' ≠ 0`, then `p ∤ v_T(coefficientPrimitive U')`. -/
theorem not_dvd_order_coefficientPrimitive_derivative (p : ℕ) [CharP κ p]
    (U : LaurentSeries κ) (hU : derivative κ U ≠ 0) :
    ¬ (p : ℤ) ∣ (coefficientPrimitive (derivative κ U)).order := by
  intro hd
  have hP : coefficientPrimitive (derivative κ U) ≠ 0 := by
    intro hzero
    apply hU
    rw [← derivative_coefficientPrimitive_derivative U, hzero, map_zero]
  apply hP
  apply HahnSeries.coeff_order_eq_zero.mp
  rw [coefficientPrimitive_derivative_coeff_charP p, ite_eq_left hd]

end

end LaurentSeries
