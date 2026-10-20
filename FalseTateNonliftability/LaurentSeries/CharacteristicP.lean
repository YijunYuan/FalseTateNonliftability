/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.CharP.Defs

/-!
# The image of differentiation of Laurent series in characteristic `p`

Let `κ` be a field of characteristic `p`. A Laurent series `h ∈ κ((T))` is the derivative of a
Laurent series if and only if its coefficients in all degrees `p * ℓ - 1`, `ℓ ∈ ℤ`, vanish.

## Main definitions

* `LaurentSeries.coefficientPrimitive h`: the Laurent series `∑ⱼ (h_{j - 1} / j) T ^ j`, whose
  coefficient is zero in every degree `j` with `(j : κ) = 0`.

## Main results

* `LaurentSeries.exists_derivative_iff`: `h = A'` for some `A ∈ κ((T))` if and only if
  `h_{p * ℓ - 1} = 0` for all `ℓ ∈ ℤ`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.4 (3).
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {κ : Type*} [Field κ]

/-- The Laurent series `∑ⱼ (h_{j - 1} / j) T ^ j`; its coefficient in every degree `j` with
`(j : κ) = 0` is zero. -/
def coefficientPrimitive (h : LaurentSeries κ) : LaurentSeries κ :=
  HahnSeries.ofSuppBddBelow (fun j : ℤ ↦ h.coeff (j - 1) / (j : κ)) <| by
    refine ⟨h.order + 1, fun j hj ↦ ?_⟩
    contrapose! hj
    rw [Function.notMem_support,
      HahnSeries.coeff_eq_zero_of_lt_order (by omega : j - 1 < h.order), zero_div]

@[simp]
theorem coefficientPrimitive_coeff (h : LaurentSeries κ) (j : ℤ) :
    (coefficientPrimitive h).coeff j = h.coeff (j - 1) / (j : κ) := rfl

/-- The coefficient of `T ^ n` in `f'` is `(n + 1) f_{n + 1}`. -/
theorem derivative_coeff (f : LaurentSeries κ) (n : ℤ) :
    (derivative κ f).coeff n = ((n + 1 : ℤ) : κ) * f.coeff (n + 1) := by
  simp [derivative, hasseDeriv_coeff, zsmul_eq_mul]

/-- Over a field of characteristic `p`, a Laurent series `h` is a derivative if and only if its
coefficients in all degrees `p * ℓ - 1`, `ℓ ∈ ℤ`, vanish. -/
theorem exists_derivative_iff (p : ℕ) [CharP κ p] (h : LaurentSeries κ) :
    (∃ A : LaurentSeries κ, derivative κ A = h) ↔
      ∀ ℓ : ℤ, h.coeff ((p : ℤ) * ℓ - 1) = 0 := by
  constructor
  · rintro ⟨A, rfl⟩ ℓ
    rw [derivative_coeff]
    simp [Int.cast_mul]
  · intro hh
    refine ⟨coefficientPrimitive h, ?_⟩
    ext n
    rw [derivative_coeff, coefficientPrimitive_coeff, add_sub_cancel_right]
    by_cases hn : ((n + 1 : ℤ) : κ) = 0
    · obtain ⟨ℓ, hℓ⟩ := (CharP.intCast_eq_zero_iff κ p (n + 1)).mp hn
      have hzero : h.coeff n = 0 := by
        have hnℓ : n = (p : ℤ) * ℓ - 1 := by omega
        simpa only [hnℓ] using hh ℓ
      simp [hn, hzero]
    · exact mul_div_cancel₀ _ hn

end

end LaurentSeries
