module

public import FalseTateNonliftability.LaurentSeries.CharacteristicP
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The kernel of Laurent-series differentiation

The kernel consists of series supported on exponents divisible by the
characteristic. Over the prime field these are precisely the pth powers.
This is the kernel clause of `nl:characteristic-p-differentiation`, used in
the coefficient arguments of Yuan, Lemma 2.3 and Proposition 4.2.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {F : Type*} [Field F]

/-- The derivative vanishes exactly when all exponents in the support are
divisible by the characteristic. This holds over arbitrary coefficient fields,
without a perfectness assumption. -/
theorem derivative_eq_zero_iff (p : ℕ) [CharP F p] (U : LaurentSeries F) :
    derivative F U = 0 ↔ ∀ n : ℤ, ¬ (p : ℤ) ∣ n → U.coeff n = 0 := by
  constructor
  · intro h n hn
    have hc := congrArg (fun f : LaurentSeries F ↦ f.coeff (n - 1)) h
    rw [derivative_coeff] at hc
    simp only [sub_add_cancel, HahnSeries.coeff_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left
      (fun hz ↦ hn ((CharP.intCast_eq_zero_iff F p n).mp hz))
  · intro h
    ext n
    rw [derivative_coeff, HahnSeries.coeff_zero]
    by_cases hn : (p : ℤ) ∣ n + 1
    · rw [(CharP.intCast_eq_zero_iff F p (n + 1)).mpr hn, zero_mul]
    · rw [h (n + 1) hn, mul_zero]

private theorem expand_zmod_eq_pow (p : ℕ) [Fact p.Prime]
    (V : PowerSeries (ZMod p)) :
    PowerSeries.expand p (Fact.out : p.Prime).ne_zero V = V ^ p := by
  simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card V

/-- Every pth power over the prime field is supported on exponents divisible
by `p`, including its possibly negative exponents. -/
theorem coeff_pow_prime_eq_zero_of_not_dvd (p : ℕ) [Fact p.Prime]
    (B : LaurentSeries (ZMod p)) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    (B ^ p).coeff n = 0 := by
  conv_lhs => rw [← single_order_mul_powerSeriesPart B]
  rw [mul_pow, HahnSeries.single_pow, ← PowerSeries.coe_pow]
  simp only [one_pow, nsmul_eq_mul, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe]
  split_ifs with hneg
  · rfl
  · rw [← expand_zmod_eq_pow]
    apply PowerSeries.coeff_expand_of_not_dvd
    intro hd
    have hcast : (p : ℤ) ∣ (((n - (p : ℤ) * B.order).natAbs : ℕ) : ℤ) := by
      exact_mod_cast hd
    rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hneg)] at hcast
    apply hn
    simpa only [sub_add_cancel] using
      dvd_add hcast (show (p : ℤ) ∣ (p : ℤ) * B.order from ⟨B.order, rfl⟩)

/-- Over the prime field the kernel of Laurent-series differentiation is
exactly the set of pth powers. No perfectness assertion for arbitrary
coefficient fields is used. -/
theorem derivative_eq_zero_iff_exists_pow (p : ℕ) [Fact p.Prime]
    (U : LaurentSeries (ZMod p)) :
    derivative (ZMod p) U = 0 ↔ ∃ B : LaurentSeries (ZMod p), B ^ p = U := by
  constructor
  · intro hU
    by_cases hzero : U = 0
    · exact ⟨0, by simp [hzero, (Fact.out : p.Prime).ne_zero]⟩
    have hs := (derivative_eq_zero_iff p U).mp hU
    have horder : (p : ℤ) ∣ U.order := by
      by_contra hn
      exact hzero (HahnSeries.coeff_order_eq_zero.mp (hs U.order hn))
    obtain ⟨q, hq⟩ := horder
    let V : PowerSeries (ZMod p) :=
      PowerSeries.mk (fun n ↦ PowerSeries.coeff (p * n) U.powerSeriesPart)
    have hexpand : PowerSeries.expand p (Fact.out : p.Prime).ne_zero V =
        U.powerSeriesPart := by
      ext n
      by_cases hn : p ∣ n
      · obtain ⟨m, rfl⟩ := hn
        rw [PowerSeries.coeff_expand_mul]
        simp [V]
      · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hn, powerSeriesPart_coeff]
        symm
        apply hs
        intro hd
        have hcast : (p : ℤ) ∣ (n : ℤ) := by
          simpa only [add_sub_cancel_left] using
            dvd_sub hd (show (p : ℤ) ∣ U.order from ⟨q, hq⟩)
        exact hn (Int.natCast_dvd_natCast.mp hcast)
    refine ⟨HahnSeries.single q 1 * (V : LaurentSeries (ZMod p)), ?_⟩
    rw [mul_pow, HahnSeries.single_pow, ← PowerSeries.coe_pow]
    simp only [one_pow, nsmul_eq_mul]
    rw [← expand_zmod_eq_pow, hexpand, ← hq]
    exact single_order_mul_powerSeriesPart U
  · rintro ⟨B, rfl⟩
    apply (derivative_eq_zero_iff p _).mpr
    exact coeff_pow_prime_eq_zero_of_not_dvd p B

end

end LaurentSeries
