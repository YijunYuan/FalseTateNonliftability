module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.CharP.Defs

/-!
# The image of Laurent-series differentiation in characteristic p

Over a field of characteristic `p`, a Laurent series is a derivative exactly
when its coefficients in degrees `p * ℓ - 1` vanish. The primitive is constructed
by dividing the coefficient in degree `j - 1` by the image of the integer `j`.

This is the coefficient argument used in Yuan, Lemma 2.3, and the image clause
of blueprint lemma `nl:characteristic-p-differentiation`.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {F : Type*} [Field F]

/-- The coefficientwise primitive with zero coefficients at integer exponents
whose image in the coefficient field vanishes. -/
def coefficientPrimitive (h : LaurentSeries F) : LaurentSeries F :=
  HahnSeries.ofSuppBddBelow (fun j : ℤ ↦ h.coeff (j - 1) / (j : F)) <| by
    refine ⟨h.order + 1, fun j hj ↦ ?_⟩
    contrapose! hj
    rw [Function.notMem_support,
      HahnSeries.coeff_eq_zero_of_lt_order (by omega : j - 1 < h.order), zero_div]

@[simp]
theorem coefficientPrimitive_coeff (h : LaurentSeries F) (j : ℤ) :
    (coefficientPrimitive h).coeff j = h.coeff (j - 1) / (j : F) := rfl

/-- The coefficient formula for the canonical Laurent-series derivative. -/
theorem derivative_coeff (h : LaurentSeries F) (n : ℤ) :
    (derivative F h).coeff n = ((n + 1 : ℤ) : F) * h.coeff (n + 1) := by
  simp [derivative, hasseDeriv_coeff, zsmul_eq_mul]

/-- A Laurent series over a field of characteristic `p` has a primitive if
and only if its coefficients in all degrees `p * ℓ - 1` vanish.

The criterion includes negative degrees and the zero series. In positive
characteristic these are exactly the degrees congruent to `-1` modulo `p`.
See Yuan, Lemma 2.3, proof of assertion (3). -/
theorem exists_derivative_iff (p : ℕ) [CharP F p] (h : LaurentSeries F) :
    (∃ A : LaurentSeries F, derivative F A = h) ↔
      ∀ ℓ : ℤ, h.coeff ((p : ℤ) * ℓ - 1) = 0 := by
  constructor
  · rintro ⟨A, rfl⟩ ℓ
    rw [derivative_coeff]
    simp [Int.cast_mul]
  · intro hh
    refine ⟨coefficientPrimitive h, ?_⟩
    ext n
    rw [derivative_coeff, coefficientPrimitive_coeff, add_sub_cancel_right]
    by_cases hn : ((n + 1 : ℤ) : F) = 0
    · obtain ⟨ℓ, hℓ⟩ := (CharP.intCast_eq_zero_iff F p (n + 1)).mp hn
      have hzero : h.coeff n = 0 := by
        have hnℓ : n = (p : ℤ) * ℓ - 1 := by omega
        simpa only [hnℓ] using hh ℓ
      simp [hn, hzero]
    · exact mul_div_cancel₀ _ hn

end

end LaurentSeries
