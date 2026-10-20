/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The derivative of Laurent series

Let `R` be a commutative ring. The derivative `d / dT` of `R((T))` (`LaurentSeries.derivative`)
sends `∑ f_j T ^ j` to `∑ (j + 1) f_{j + 1} T ^ j`. It satisfies the Leibniz rule and restricts to
the derivative of power series.

Let `κ` be a field of characteristic `p`. A Laurent series `h ∈ κ((T))` is a derivative if and
only if its coefficients in all degrees `p * ℓ - 1`, `ℓ ∈ ℤ`, vanish. A Laurent series `U` satisfies
`U' = 0` if and only if it is supported on exponents divisible by `p`; if `κ` is perfect, the kernel
of `d / dT` is `κ((T)) ^ p`. Deleting from `U` the terms whose exponents are divisible by `p` gives
the primitive `coefficientPrimitive U'` of `U'`; if `U' ≠ 0`, it has order `v_T(U') + 1`, which is
not divisible by `p`.

## Main definitions

* `LaurentSeries.coefficientPrimitive h`: the Laurent series `∑ⱼ (h_{j - 1} / j) T ^ j` over a
  field, whose coefficient is zero in every degree `j` with `(j : κ) = 0`.

## Main results

* `LaurentSeries.coeff_derivative`: the coefficient of `T ^ j` in `f'` is `(j + 1) f_{j + 1}`.
* `LaurentSeries.derivative_mul`, `LaurentSeries.derivative_pow_succ`,
  `LaurentSeries.derivative_units_zpow`: the Leibniz rule and the power rules.
* `LaurentSeries.derivative_ofPowerSeries`: restriction to power series.
* `LaurentSeries.exists_derivative_iff`: `h = A'` for some `A ∈ κ((T))` if and only if
  `h_{p * ℓ - 1} = 0` for all `ℓ ∈ ℤ`.
* `LaurentSeries.derivative_eq_zero_iff`, `LaurentSeries.derivative_eq_zero_iff_exists_pow`: the
  kernel of `d / dT` in characteristic `p`.
* `LaurentSeries.derivative_coefficientPrimitive_derivative`,
  `LaurentSeries.order_coefficientPrimitive_derivative`,
  `LaurentSeries.not_dvd_order_coefficientPrimitive_derivative`: the primitive
  `coefficientPrimitive U'` of `U'`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.4 (3), Lemma 4.2 and Proposition 4.3.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The coefficient of `T ^ j` in `f'` is `(j + 1) f_{j + 1}`. -/
theorem coeff_derivative (f : LaurentSeries R) (j : ℤ) :
    (derivative R f).coeff j = ((j + 1 : ℤ) : R) * f.coeff (j + 1) := by
  simp [derivative, hasseDeriv_coeff, zsmul_eq_mul]

@[simp]
theorem derivative_single (j : ℤ) (b : R) :
    derivative R (HahnSeries.single j b) = HahnSeries.single (j - 1) ((j : R) * b) := by
  simp [derivative, hasseDeriv_single, zsmul_eq_mul]

@[simp]
theorem derivative_C (b : R) : derivative R (HahnSeries.C b) = 0 := by
  rw [HahnSeries.C_apply, derivative_single]
  simp

/-- The derivative of Laurent series restricts to the derivative of power series. -/
theorem derivative_ofPowerSeries (H : PowerSeries R) :
    derivative R (HahnSeries.ofPowerSeries ℤ R H) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.derivative H) := by
  ext j
  rw [coeff_derivative]
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, show ((n : ℤ) + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_derivative]
    push_cast
    exact mul_comm _ _
  | negSucc n =>
    cases n with
    | zero => simp [PowerSeries.coeff_coe]
    | succ n =>
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe,
        ite_eq_left (by omega), ite_eq_left (by omega), mul_zero]

/-- If `H'(0)` is a unit, then the derivative of the power series `H` is a unit. -/
theorem isUnit_derivative_ofPowerSeries (H : PowerSeries R) (hlinear : IsUnit (H.coeff 1)) :
    IsUnit (derivative R (HahnSeries.ofPowerSeries ℤ R H)) := by
  rw [derivative_ofPowerSeries]
  apply IsUnit.map (HahnSeries.ofPowerSeries ℤ R)
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hlinear

/-! ### The Leibniz rule -/

/-- The coefficient of `T ^ n` in `T f'` is `n f_n`. -/
private theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (HahnSeries.single 1 1 * derivative R f).coeff n = (n : R) * f.coeff n := by
  rw [HahnSeries.coeff_single_mul, coeff_derivative, one_mul, sub_add_cancel]

private theorem support_single_one_mul_derivative_subset (f : LaurentSeries R) :
    (HahnSeries.single 1 1 * derivative R f).support ⊆ f.support := fun n hn ↦ by
  rw [HahnSeries.mem_support, coeff_single_one_mul_derivative] at hn
  exact right_ne_zero_of_mul hn

/-- The Leibniz rule `(f g)' = f' g + f g'`. -/
theorem derivative_mul (f g : LaurentSeries R) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  -- `T (f g)'` and `T f' g + f T g'` have the coefficient `n ∑_{i + j = n} f_i g_j` at `T ^ n`.
  have h : HahnSeries.single 1 1 * derivative R (f * g) =
      HahnSeries.single 1 1 * (derivative R f * g + f * derivative R g) := by
    ext n
    rw [mul_add, ← mul_assoc, mul_left_comm, HahnSeries.coeff_add,
      coeff_single_one_mul_derivative,
      HahnSeries.coeff_mul_left' f.isPWO_support (support_single_one_mul_derivative_subset f),
      HahnSeries.coeff_mul_right' g.isPWO_support (support_single_one_mul_derivative_subset g),
      HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [coeff_single_one_mul_derivative, coeff_single_one_mul_derivative,
      ← (Finset.mem_antidiagonal.mp hij).2.2, Int.cast_add]
    ring
  have hT : (HahnSeries.single (-1) 1 * HahnSeries.single 1 1 : LaurentSeries R) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  rw [← one_mul (derivative R (f * g)), ← hT, mul_assoc, h, ← mul_assoc, hT, one_mul]

@[simp]
theorem derivative_one : derivative R (1 : LaurentSeries R) = 0 := by
  simpa only [HahnSeries.C_one] using derivative_C (R := R) 1

/-- The power rule `(f ^ (n + 1))' = (n + 1) f ^ n f'`. -/
theorem derivative_pow_succ (f : LaurentSeries R) (n : ℕ) :
    derivative R (f ^ (n + 1)) = ((n + 1 : ℕ) : LaurentSeries R) * f ^ n * derivative R f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ f (n + 1), derivative_mul, ih, pow_succ]
    push_cast
    ring

/-- The derivative of the inverse of a unit `u` is `-u⁻² u'`. -/
theorem derivative_units_inv (u : (LaurentSeries R)ˣ) :
    derivative R (↑(u⁻¹) : LaurentSeries R) =
      -((↑(u⁻¹) : LaurentSeries R) ^ 2 * derivative R (u : LaurentSeries R)) := by
  apply eq_neg_of_add_eq_zero_left
  calc
    _ = ((↑(u⁻¹) : LaurentSeries R) * ↑u) * derivative R (↑(u⁻¹) : LaurentSeries R) +
        (↑(u⁻¹) * ↑(u⁻¹)) * derivative R (u : LaurentSeries R) := by
      simp only [Units.inv_mul, one_mul, pow_two]
    _ = (↑(u⁻¹) : LaurentSeries R) * derivative R ((↑(u⁻¹) : LaurentSeries R) * ↑u) := by
      rw [derivative_mul]
      ring
    _ = 0 := by simp only [Units.inv_mul, derivative_one, mul_zero]

/-- The power rule `(u ^ j)' = j u ^ (j - 1) u'` for a unit `u` and `j ∈ ℤ`. -/
theorem derivative_units_zpow (u : (LaurentSeries R)ˣ) (j : ℤ) :
    derivative R (↑(u ^ j) : LaurentSeries R) =
      (j : LaurentSeries R) * (↑(u ^ (j - 1)) : LaurentSeries R) *
        derivative R (u : LaurentSeries R) := by
  cases j with
  | ofNat n =>
    cases n with
    | zero =>
      simpa only [Int.ofNat_eq_natCast, Nat.cast_zero, zpow_zero, Units.val_one,
        Int.cast_zero, zero_mul] using
        (derivative_one (R := R))
    | succ n =>
      simpa only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one, Int.natCast_add, Int.natCast_one,
        add_sub_cancel_right, zpow_natCast, Units.val_pow_eq_pow_val,
        Int.cast_add, Int.cast_natCast, Int.cast_one, zpow_add, zpow_one, Units.val_mul,
        pow_succ, Nat.cast_add, Nat.cast_one] using derivative_pow_succ (u : LaurentSeries R) n
  | negSucc n =>
    have hj : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    have he : -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) := by omega
    rw [hj, he]
    simp only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [derivative_pow_succ, derivative_units_inv]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [pow_add]
    ring

end

end LaurentSeries

/-! ### The image of the derivative in characteristic `p` -/

section CharacteristicP

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

/-- Over a field of characteristic `p`, a Laurent series `h` is a derivative if and only if its
coefficients in all degrees `p * ℓ - 1`, `ℓ ∈ ℤ`, vanish. -/
theorem exists_derivative_iff (p : ℕ) [CharP κ p] (h : LaurentSeries κ) :
    (∃ A : LaurentSeries κ, derivative κ A = h) ↔
      ∀ ℓ : ℤ, h.coeff ((p : ℤ) * ℓ - 1) = 0 := by
  constructor
  · rintro ⟨A, rfl⟩ ℓ
    rw [coeff_derivative]
    simp [Int.cast_mul]
  · intro hh
    refine ⟨coefficientPrimitive h, ?_⟩
    ext n
    rw [coeff_derivative, coefficientPrimitive_coeff, add_sub_cancel_right]
    by_cases hn : ((n + 1 : ℤ) : κ) = 0
    · obtain ⟨ℓ, hℓ⟩ := (CharP.intCast_eq_zero_iff κ p (n + 1)).mp hn
      have hzero : h.coeff n = 0 := by
        have hnℓ : n = (p : ℤ) * ℓ - 1 := by omega
        simpa only [hnℓ] using hh ℓ
      simp [hn, hzero]
    · exact mul_div_cancel₀ _ hn

end

end LaurentSeries

end CharacteristicP

/-! ### The kernel of the derivative in characteristic `p` -/

section FrobeniusKernel

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
    rw [coeff_derivative] at hc
    simp only [sub_add_cancel, HahnSeries.coeff_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left
      (fun hz ↦ hn ((CharP.intCast_eq_zero_iff κ p n).mp hz))
  · intro h
    ext n
    rw [coeff_derivative, HahnSeries.coeff_zero]
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

end FrobeniusKernel

/-! ### Normalized primitives in characteristic `p` -/

section PrimitiveNormalization

namespace LaurentSeries

noncomputable section

variable {κ : Type*} [Field κ]

/-- `coefficientPrimitive U'` is obtained from `U` by deleting the terms in the degrees `n` with
`(n : κ) = 0`. -/
theorem coefficientPrimitive_derivative_coeff [DecidableEq κ] (U : LaurentSeries κ) (n : ℤ) :
    (coefficientPrimitive (derivative κ U)).coeff n =
      if (n : κ) = 0 then 0 else U.coeff n := by
  rw [coefficientPrimitive_coeff, coeff_derivative]
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
  rw [coeff_derivative, coefficientPrimitive_derivative_coeff, coeff_derivative]
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
    rw [coeff_derivative, hz, zero_mul]
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

end PrimitiveNormalization
