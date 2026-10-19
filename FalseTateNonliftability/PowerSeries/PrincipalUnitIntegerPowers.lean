module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Field.ZMod

/-!
# Integer powers of principal units

Order estimates for integer powers of actual units of `PowerSeries (ZMod p)`.
The order takes values in `ℕ∞`, so the identity unit is included throughout.
These are the algebraic estimates underlying Yuan, proof of Lemma 4.1,
equation (4.2); see blueprint `nl:principal-unit-integer-powers`.
-/

@[expose] public section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- Iterated Frobenius expresses a prime-power difference as a prime power. -/
theorem pow_prime_pow_sub_one (z : PowerSeries (ZMod p)) (r : ℕ) :
    z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r) := by
  have : CharP (PowerSeries (ZMod p)) p := charP_of_injective_ringHom C_injective p
  simpa using (sub_pow_char_pow (p := p) z 1 r).symm

/-- Prime-power differences scale order, including the infinite order of zero. -/
theorem order_pow_prime_pow_sub_one (z : PowerSeries (ZMod p)) (r : ℕ) :
    (z ^ (p ^ r) - 1).order = (p ^ r) • (z - 1).order := by
  rw [pow_prime_pow_sub_one, order_pow]

/-- A power with exponent prime to the characteristic preserves the order of a
principal-unit difference. -/
theorem order_pow_sub_one_of_not_dvd (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (a : ℕ) (ha : ¬ p ∣ a) :
    (z ^ a - 1).order = (z - 1).order := by
  have hsum : IsUnit (∑ i ∈ Finset.range a, z ^ i) := by
    rw [isUnit_iff_constantCoeff]
    simpa [map_sum, hz] using
      (isUnit_iff_ne_zero.mpr (mt (ZMod.natCast_eq_zero_iff a p).mp ha) :
        IsUnit (a : ZMod p))
  rw [← mul_geom_sum, order_mul, order_zero_of_isUnit hsum, add_zero]

/-- Negating an integer exponent changes the difference by a unit factor. -/
theorem coe_zpow_neg_sub_one (z : (PowerSeries (ZMod p))ˣ) (a : ℤ) :
    ((z ^ (-a) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1 =
      -((z ^ (-a) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
        (((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1) := by
  have hmul : ((z ^ (-a) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
      ((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) = 1 := by
    rw [← Units.val_mul, ← zpow_add]
    simp
  rw [neg_mul, mul_sub, hmul, mul_one, neg_sub]

/-- The orders of a unit difference for opposite integer exponents agree. -/
theorem order_coe_zpow_neg_sub_one (z : (PowerSeries (ZMod p))ˣ) (a : ℤ) :
    (((z ^ (-a) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1).order =
      (((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1).order := by
  rw [coe_zpow_neg_sub_one, order_mul, order_neg,
    order_zero_of_isUnit (z ^ (-a)).isUnit, zero_add]

/-- Integer powers prime to `p` preserve the order of a principal-unit difference. -/
theorem order_coe_zpow_sub_one_of_not_dvd (z : (PowerSeries (ZMod p))ˣ)
    (hz : constantCoeff (z : PowerSeries (ZMod p)) = 1) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) :
    (((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1).order =
      ((z : PowerSeries (ZMod p)) - 1).order := by
  cases a with
  | ofNat d =>
      change (((z ^ (d : ℤ) : (PowerSeries (ZMod p))ˣ) :
        PowerSeries (ZMod p)) - 1).order = _
      simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
        order_pow_sub_one_of_not_dvd (z : PowerSeries (ZMod p)) hz d
          (mt Int.natCast_dvd_natCast.mpr ha)
  | negSucc d =>
      change ¬ (p : ℤ) ∣ -((d + 1 : ℕ) : ℤ) at ha
      change (((z ^ (-((d + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) :
        PowerSeries (ZMod p)) - 1).order = _
      rw [order_coe_zpow_neg_sub_one]
      simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
        order_pow_sub_one_of_not_dvd (z : PowerSeries (ZMod p)) hz (d + 1)
          (fun h ↦ ha (dvd_neg.mpr (Int.natCast_dvd_natCast.mpr h)))

/-- Every integer-power difference is divisible by the original unit difference. -/
theorem sub_one_dvd_coe_zpow_sub_one (z : (PowerSeries (ZMod p))ˣ) (a : ℤ) :
    (z : PowerSeries (ZMod p)) - 1 ∣
      ((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1 := by
  cases a with
  | ofNat d =>
      change (z : PowerSeries (ZMod p)) - 1 ∣
        ((z ^ (d : ℤ) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1
      simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
        sub_one_dvd_pow_sub_one (z : PowerSeries (ZMod p)) d
  | negSucc d =>
      change (z : PowerSeries (ZMod p)) - 1 ∣
        ((z ^ (-((d + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) :
          PowerSeries (ZMod p)) - 1
      rw [coe_zpow_neg_sub_one]
      apply dvd_mul_of_dvd_right
      simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
        sub_one_dvd_pow_sub_one (z : PowerSeries (ZMod p)) (d + 1)

/-- Congruent integer exponents give a difference of order at least the
corresponding prime-power multiple of the original order. No finiteness
assumption on that order is needed. -/
theorem prime_pow_smul_order_le_order_coe_zpow_sub
    (z : (PowerSeries (ZMod p))ˣ) (a b : ℤ) (r : ℕ)
    (hab : (p : ℤ) ^ r ∣ a - b) :
    (p ^ r) • ((z : PowerSeries (ZMod p)) - 1).order ≤
      (((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) -
        ((z ^ b : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))).order := by
  obtain ⟨d, hd⟩ := hab
  have ha : a = b + d * ((p ^ r : ℕ) : ℤ) := by
    calc
      a = (p : ℤ) ^ r * d + b := sub_eq_iff_eq_add.mp hd
      _ = b + d * ((p ^ r : ℕ) : ℤ) := by rw [Int.natCast_pow, mul_comm, add_comm]
  have hpow : (((z ^ d : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) ^
      (p ^ r)) = ((z ^ (d * ((p ^ r : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) :
        PowerSeries (ZMod p)) := by
    rw [zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  have hfactor : ((z ^ a : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) -
      ((z ^ b : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) =
      ((z ^ b : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
        ((((z ^ d : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) - 1) ^
          (p ^ r)) := by
    rw [← pow_prime_pow_sub_one, hpow, ha, zpow_add, Units.val_mul, mul_sub, mul_one]
  obtain ⟨w, hw⟩ := pow_dvd_pow_of_dvd (sub_one_dvd_coe_zpow_sub_one z d) (p ^ r)
  rw [hfactor, order_mul, order_zero_of_isUnit (z ^ b).isUnit, zero_add, hw, order_mul,
    ← order_pow]
  exact le_add_of_nonneg_right zero_le

end PowerSeries
