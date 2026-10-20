/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.CharacteristicP
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The kernel of differentiation of Laurent series in characteristic `p`

Let `κ` be a field of characteristic `p`. A Laurent series `U ∈ κ((T))` satisfies `U' = 0` if and
only if `U` is supported on exponents divisible by `p`. Every `p`-th power has this property, and
if `κ` is perfect, then the kernel of `d / dT` on `κ((T))` is exactly `κ((T)) ^ p`.

## Main results

* `LaurentSeries.derivative_eq_zero_iff`: `U' = 0` iff `U_n = 0` for all `n` with `p ∤ n`.
* `LaurentSeries.coeff_pow_prime_eq_zero_of_not_dvd`: `(B ^ p)_n = 0` for all `n` with `p ∤ n`.
* `LaurentSeries.derivative_eq_zero_iff_exists_pow`: over a perfect field, `U' = 0` iff
  `U = B ^ p` for some `B ∈ κ((T))`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.2 and Proposition 4.3.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {κ : Type*} [Field κ]

/-- Over a field of characteristic `p`, `U' = 0` if and only if `U_n = 0` for all `n ∈ ℤ` with
`p ∤ n`. -/
theorem derivative_eq_zero_iff (p : ℕ) [CharP κ p] (U : LaurentSeries κ) :
    derivative κ U = 0 ↔ ∀ n : ℤ, ¬ (p : ℤ) ∣ n → U.coeff n = 0 := by
  constructor
  · intro h n hn
    have hc := congrArg (fun f : LaurentSeries κ ↦ f.coeff (n - 1)) h
    rw [derivative_coeff] at hc
    simp only [sub_add_cancel, HahnSeries.coeff_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left
      (fun hz ↦ hn ((CharP.intCast_eq_zero_iff κ p n).mp hz))
  · intro h
    ext n
    rw [derivative_coeff, HahnSeries.coeff_zero]
    by_cases hn : (p : ℤ) ∣ n + 1
    · rw [(CharP.intCast_eq_zero_iff κ p (n + 1)).mpr hn, zero_mul]
    · rw [h (n + 1) hn, mul_zero]

/-- Over a field of characteristic `p`, the coefficients of `B ^ p` vanish in all degrees not
divisible by `p`. -/
theorem coeff_pow_prime_eq_zero_of_not_dvd (p : ℕ) [Fact p.Prime] [CharP κ p]
    (B : LaurentSeries κ) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    (B ^ p).coeff n = 0 := by
  have hp := (Fact.out : p.Prime).ne_zero
  conv_lhs => rw [← single_order_mul_powerSeriesPart B]
  rw [mul_pow, HahnSeries.single_pow, ← PowerSeries.coe_pow,
    ← PowerSeries.map_frobenius_expand p hp]
  simp only [one_pow, nsmul_eq_mul, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe]
  split_ifs with hneg
  · rfl
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_expand_of_not_dvd, map_zero]
    intro hd
    have hcast : (p : ℤ) ∣ (((n - (p : ℤ) * B.order).natAbs : ℕ) : ℤ) := by
      exact_mod_cast hd
    rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hneg)] at hcast
    apply hn
    simpa only [sub_add_cancel] using
      dvd_add hcast (show (p : ℤ) ∣ (p : ℤ) * B.order from ⟨B.order, rfl⟩)

/-- Over a perfect field of characteristic `p`, the kernel of differentiation on `κ((T))` is
`κ((T)) ^ p`. -/
theorem derivative_eq_zero_iff_exists_pow (p : ℕ) [Fact p.Prime] [CharP κ p] [PerfectRing κ p]
    (U : LaurentSeries κ) :
    derivative κ U = 0 ↔ ∃ B : LaurentSeries κ, B ^ p = U := by
  have hp := (Fact.out : p.Prime).ne_zero
  constructor
  · intro hU
    by_cases hzero : U = 0
    · exact ⟨0, by simp [hzero, hp]⟩
    have hs := (derivative_eq_zero_iff p U).mp hU
    have horder : (p : ℤ) ∣ U.order := by
      by_contra hn
      exact hzero (HahnSeries.coeff_order_eq_zero.mp (hs U.order hn))
    obtain ⟨q, hq⟩ := horder
    let V : PowerSeries κ :=
      PowerSeries.mk (fun n ↦ PowerSeries.coeff (p * n) U.powerSeriesPart)
    have hexpand : PowerSeries.expand p hp V = U.powerSeriesPart := by
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
    let W : PowerSeries κ := PowerSeries.map ((frobeniusEquiv κ p).symm : κ →+* κ) V
    have hW : W ^ p = U.powerSeriesPart := by
      rw [← PowerSeries.map_frobenius_expand p hp, PowerSeries.map_expand, ← hexpand]
      congr 1
      ext n
      simp [W]
    refine ⟨HahnSeries.single q 1 * (W : LaurentSeries κ), ?_⟩
    rw [mul_pow, HahnSeries.single_pow, ← PowerSeries.coe_pow, hW]
    simp only [one_pow, nsmul_eq_mul, ← hq]
    exact single_order_mul_powerSeriesPart U
  · rintro ⟨B, rfl⟩
    exact (derivative_eq_zero_iff p _).mpr (coeff_pow_prime_eq_zero_of_not_dvd p B)

end

end LaurentSeries
