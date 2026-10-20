/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Natural powers of principal units of `κ⟦T⟧` in characteristic `p`

Let `κ` be a field of characteristic `p` and `z ∈ κ⟦T⟧`. Then `z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r)`,
so `v_T(z ^ (p ^ r) - 1) = p ^ r v_T(z - 1)`; and if `z` is a principal unit and `p ∤ a`, then
`v_T(z ^ a - 1) = v_T(z - 1)`. Orders take values in `ℕ∞`, so `z = 1` is included.

## Main results

* `PowerSeries.order_pow_prime_pow_sub_one`: `v_T(z ^ (p ^ r) - 1) = p ^ r • v_T(z - 1)`.
* `PowerSeries.order_pow_sub_one_of_not_dvd`: `v_T(z ^ a - 1) = v_T(z - 1)` if `z(0) = 1` and
  `p ∤ a`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.1 and Lemma 4.2, equation (4.3).
-/

@[expose] public section

namespace PowerSeries

variable {κ : Type*} [Field κ] {p : ℕ} [CharP κ p]

/-- In characteristic `p`, `z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r)`. -/
theorem pow_prime_pow_sub_one [Fact p.Prime] (z : PowerSeries κ) (r : ℕ) :
    z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r) := by
  have : CharP (PowerSeries κ) p := charP_of_injective_ringHom C_injective p
  simpa using (sub_pow_char_pow (p := p) z 1 r).symm

/-- In characteristic `p`, `v_T(z ^ (p ^ r) - 1) = p ^ r • v_T(z - 1)`. -/
theorem order_pow_prime_pow_sub_one [Fact p.Prime] (z : PowerSeries κ) (r : ℕ) :
    (z ^ (p ^ r) - 1).order = (p ^ r) • (z - 1).order := by
  rw [pow_prime_pow_sub_one, order_pow]

/-- If `z(0) = 1` and `p ∤ a`, then `v_T(z ^ a - 1) = v_T(z - 1)`. -/
theorem order_pow_sub_one_of_not_dvd (z : PowerSeries κ) (hz : constantCoeff z = 1) (a : ℕ)
    (ha : ¬ p ∣ a) : (z ^ a - 1).order = (z - 1).order := by
  have hsum : IsUnit (∑ i ∈ Finset.range a, z ^ i) := by
    rw [isUnit_iff_constantCoeff]
    simpa [map_sum, hz] using
      (isUnit_iff_ne_zero.mpr (mt (CharP.cast_eq_zero_iff κ p a).mp ha) : IsUnit (a : κ))
  rw [← mul_geom_sum, order_mul, order_zero_of_isUnit hsum, add_zero]

end PowerSeries
