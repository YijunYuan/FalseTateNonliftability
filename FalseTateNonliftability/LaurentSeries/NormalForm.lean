/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Ramification numbers, normal forms and their growth under `p`-th powers

Let `k` be a field and let `f ∈ T k⟦T⟧` have invertible linear coefficient, so that
`σ : x ↦ x(f)` is a continuous automorphism of `k((T))` with `σ T = f`. The ramification number
of `σ` is `i(σ) = v_T(f - T) - 1`. It does not depend on the uniformizer: replacing `T` by
`T' = w(T)` replaces `f` by the conjugate `w ∘ f ∘ w^{∘-1}`, which has the same ramification
number.

Let `k` have characteristic `p`. If `σ T = T + α T ^ (d + 1) + β T ^ ℓ + O(T ^ (ℓ + 1))` with
`α, β ≠ 0`, `d + 2 ≤ ℓ ≤ 2 d` and `d ≡ ℓ ≡ -1 (mod p)`, then `i(σ ^ p) = ℓ + (p - 1) d - 1`,
which is smaller than `(p + 1) d` (Yuan, Lemma 3.3). Consequently, if `d = i(σ) ≡ -1 (mod p)` and
`i(σ ^ p) ≥ (p + 1) d`, the coefficients of `σ T` in degrees `d + 2, …, 2 d` can be removed one
by one by the coordinate changes `T' = T + t T ^ q`, and in a suitable uniformizer
`σ T = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ≠ 0` (Yuan, Theorem 3.4).

For every `f = T + O(T ^ 2)` in characteristic `p`, `i(σ ^ p) ≥ p i(σ)`. If `σ` has infinite
order, then `σ ^ n ≠ 1` for every `n > 0`, so the ramification numbers `d_n = i(σ ^ (p ^ n))` are
positive integers; they satisfy `d_(n+1) ≥ p d_n`, hence strictly increase and tend to infinity.

## Main definitions

* `PowerSeries.ramificationNumber f`: the integer `v_T(f - T) - 1`.
* `LaurentSeries.substSubOne g`: the `R`-linear operator `x ↦ x(g) - x` on `R((T))`.

## Main results

* `LaurentSeries.substEquiv_conj`: `x ↦ x(w ∘ f ∘ w^{∘-1})` is the conjugate of `x ↦ x(f)` by
  `x ↦ x(w)`.
* `LaurentSeries.substEquiv_iterate`: `x ↦ x(f^{∘n})` is the `n`-th power of `x ↦ x(f)`.
* `LaurentSeries.substSubOne_pow_mem`: if `g = T + O(T ^ (d + 1))`, then `x ↦ x(g) - x` applied
  `n` times raises `O(T ^ m)` to `O(T ^ (m + n d))` (Yuan, Lemma 3.2).
* `LaurentSeries.substSubOne_pow_char_apply`: in characteristic `p`, `(σ - 1) ^ p = σ ^ p - 1`.
* `PowerSeries.ramificationNumber_conj`: the ramification number does not depend on the
  uniformizer (Yuan, §3.2).
* `PowerSeries.ramificationNumber_iterate_eq_of_resonant`: a nonzero resonant coefficient
  determines `i(σ ^ p)` (Yuan, Lemma 3.3).
* `PowerSeries.exists_normalForm`: the normal form `T + α T ^ (d + 1) + O(T ^ (2 d + 1))`
  (Yuan, Theorem 3.4).
* `PowerSeries.mul_ramificationNumber_le_ramificationNumber_iterate`: `p i(σ) ≤ i(σ ^ p)`.
* `PowerSeries.one_le_ramificationNumber_iterate`: `i(σ ^ n) ≥ 1` for `n > 0` if `σ` has infinite
  order.
* `PowerSeries.strictMono_ramificationNumber_iterate_pow`: `n ↦ i(σ ^ (p ^ n))` is strictly
  increasing.
* `PowerSeries.tendsto_ramificationNumber_iterate_pow_atTop`: `i(σ ^ (p ^ n)) → ∞`.

## Implementation notes

`PowerSeries.ramificationNumber f` is the integer `v_T(f - T) - 1`, where `v_T` is
`HahnSeries.order`, so that `v_T(0) = 0`. For `f = X`, where the paper has `i(σ) = +∞`, it is
`-1`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  §3.2 (the ramification number), Lemma 3.3, Theorem 3.4 and the proof of Lemma 4.2 (the growth
  of `d_j`).
-/

@[expose] public section

noncomputable section

/-! ### Normal forms -/

section NormalForm

namespace LaurentSeries

section CommRing

variable {R : Type*} [CommRing R]

private theorem constantCoeff_eq_zero_and_coeff_one_eq_one {f : PowerSeries R}
    (h : HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup 2) :
    f.constantCoeff = 0 ∧ f.coeff 1 = 1 := by
  have h0 := (mem_orderAddSubgroup_iff_coeff 2 _).mp h 0 (by omega)
  have h1 := (mem_orderAddSubgroup_iff_coeff 2 _).mp h 1 (by omega)
  simp only [HahnSeries.coeff_sub, PowerSeries.coeff_coe, HahnSeries.coeff_single] at h0 h1
  simp only [lt_self_iff_false, ite_false, Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, zero_ne_one, sub_zero] at h0
  simp only [Int.reduceLT, ite_false, Int.natAbs_one, ite_true, sub_eq_zero] at h1
  exact ⟨h0, h1⟩

end CommRing

end LaurentSeries

namespace PowerSeries

open LaurentSeries

section CommRing

variable {R : Type*} [CommRing R]

/-- The ramification number `v_T(f - T) - 1` of a power series `f` (Yuan, §3.2). If a continuous
automorphism `σ` of `k((T))` sends `T` to `f`, this is the ramification number `i(σ)`. It is `-1`
for `f = X`, where `i(σ) = ∞`. -/
def ramificationNumber (f : R⟦X⟧) : ℤ :=
  (HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1).order - 1

/-- The ramification number of `X` is `-1`. -/
@[simp]
theorem ramificationNumber_X : (X : R⟦X⟧).ramificationNumber = -1 := by
  simp [ramificationNumber, HahnSeries.ofPowerSeries_X]

/-- The ramification number of a power series is at least `-1`. -/
theorem neg_one_le_ramificationNumber (f : R⟦X⟧) : -1 ≤ f.ramificationNumber := by
  rw [ramificationNumber, ← HahnSeries.ofPowerSeries_X, ← map_sub]
  by_cases h : HahnSeries.ofPowerSeries ℤ R (f - X) = 0
  · rw [h, HahnSeries.order_zero]
    omega
  · have h0 : ((0 : ℤ) : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ R (f - X)).orderTop :=
      ofPowerSeries_mem_orderAddSubgroup_zero (f - X)
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h, WithTop.coe_le_coe] at h0
    omega

/-- `f - T = O(T ^ (i + 1))` for the ramification number `i` of `f`. -/
theorem ofPowerSeries_sub_X_mem_orderAddSubgroup (f : R⟦X⟧) :
    HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup (f.ramificationNumber + 1) := by
  rw [ramificationNumber, sub_add_cancel]
  exact mem_orderAddSubgroup_order _

/-- For `f ≠ X`, the order of `f - T` is `i + 1`, where `i` is the ramification number of `f`. -/
theorem orderTop_ofPowerSeries_sub_X {f : R⟦X⟧} (hf : f ≠ X) :
    (HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1).orderTop =
      ((f.ramificationNumber + 1 : ℤ) : WithTop ℤ) := by
  have hne : HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1 ≠ 0 := by
    rw [← HahnSeries.ofPowerSeries_X, ← map_sub]
    exact (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr (sub_ne_zero.mpr hf)
  rw [ramificationNumber, sub_add_cancel, HahnSeries.order_eq_orderTop_of_ne_zero hne]

/-- For `f ≠ X`, `d ≤ i(f)` if and only if `f - T = O(T ^ (d + 1))`. -/
theorem le_ramificationNumber_iff {f : R⟦X⟧} (hf : f ≠ X) {d : ℤ} :
    d ≤ f.ramificationNumber ↔
      HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) := by
  rw [mem_orderAddSubgroup, orderTop_ofPowerSeries_sub_X hf, WithTop.coe_le_coe]
  omega

/-- The ramification number is positive exactly for the series `f ≠ X` in `X + X ^ 2 R⟦X⟧`. -/
theorem one_le_ramificationNumber_iff {f : R⟦X⟧} :
    1 ≤ f.ramificationNumber ↔ f ≠ X ∧ f.constantCoeff = 0 ∧ f.coeff 1 = 1 := by
  constructor
  · intro h
    have hX : f ≠ X := by
      rintro rfl
      simp at h
    exact ⟨hX, constantCoeff_eq_zero_and_coeff_one_eq_one ((le_ramificationNumber_iff hX).mp h)⟩
  · rintro ⟨hX, h0, h1⟩
    rw [le_ramificationNumber_iff hX, show (1 : ℤ) + 1 = 2 by norm_num]
    simpa only [h1] using ofPowerSeries_sub_linear_mem_two h0

/-- A series `f` with `f(0) = 0` and `f'(0) ≠ 1` has ramification number `0`. -/
theorem ramificationNumber_eq_zero {f : R⟦X⟧} (hf : f.constantCoeff = 0) (hf1 : f.coeff 1 ≠ 1) :
    f.ramificationNumber = 0 := by
  have h := order_eq_of_sub_single_mem (sub_ne_zero.mpr hf1) (m := 1)
    (f := HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) 1) (by
      rw [sub_sub, ← HahnSeries.single_add, add_sub_cancel]
      exact ofPowerSeries_sub_linear_mem_two hf)
  rw [ramificationNumber, h, sub_self]

end CommRing

end PowerSeries

namespace LaurentSeries

section Subst

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]

private theorem substEquiv_X_left : substEquiv (PowerSeries.X : PowerSeries R) = AlgEquiv.refl :=
  AlgEquiv.ext fun x ↦ by
    rw [substEquiv_apply PowerSeries.constantCoeff_X
      (by rw [PowerSeries.coeff_one_X]; exact isUnit_one), HahnSeries.ofPowerSeries_X,
      subst_X_left_apply]
    rfl

/-- Let `w, f` have zero constant term and invertible linear coefficient. Then
`x ↦ x(w ∘ f ∘ w^{∘-1})` is `W⁻¹ ∘ F ∘ W`, where `F : x ↦ x(f)` and `W : x ↦ x(w)`. -/
theorem substEquiv_conj {w f : PowerSeries R} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) (hf : f.constantCoeff = 0) (hf' : IsUnit (f.coeff 1)) :
    substEquiv (PowerSeries.conj w f) =
      ((substEquiv w).trans (substEquiv f)).trans (substEquiv w).symm := by
  have h0 : PowerSeries.constantCoeff (w.subst f) = 0 := by
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero' hf, hw]
  have h1 : IsUnit (PowerSeries.coeff 1 (w.subst f)) := by
    rw [PowerSeries.coeff_one_subst hf]
    exact hw'.mul hf'
  rw [PowerSeries.conj, substEquiv_subst (PowerSeries.constantCoeff_compInv w)
      (PowerSeries.isUnit_coeff_one_compInv w) h0 h1, substEquiv_subst hf hf' hw hw',
    PowerSeries.compInv_eq_substInvOfIsUnit hw', ← substEquiv_symm hw hw']

/-- Let `w, f` have zero constant term and invertible linear coefficient. Then
`w ∘ f ∘ w^{∘-1} = W⁻¹(f(w))`, where `W : x ↦ x(w)`. -/
theorem ofPowerSeries_conj {w f : PowerSeries R} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) (hf : f.constantCoeff = 0) (hf' : IsUnit (f.coeff 1)) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.conj w f) =
      (substEquiv w).symm (substEquiv f (HahnSeries.ofPowerSeries ℤ R w)) := by
  rw [← substEquiv_X (PowerSeries.constantCoeff_conj hw hf)
      (PowerSeries.isUnit_coeff_one_conj hw' hf hf'), substEquiv_conj hw hw' hf hf',
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, substEquiv_X hw hw']

/-- For `f` with zero constant term and invertible linear coefficient, `x ↦ x(f^{∘n})` is the
`n`-th power of `x ↦ x(f)`. -/
theorem substEquiv_iterate {f : PowerSeries R} (hf : f.constantCoeff = 0)
    (hf' : IsUnit (f.coeff 1)) (n : ℕ) :
    substEquiv (PowerSeries.iterate f n) = substEquiv f ^ n := by
  induction n with
  | zero =>
    rw [PowerSeries.iterate_zero, pow_zero]
    exact substEquiv_X_left
  | succ n ih =>
    rw [PowerSeries.iterate_succ, substEquiv_subst hf hf' (PowerSeries.constantCoeff_iterate hf n)
      (by rw [PowerSeries.coeff_one_iterate hf]; exact hf'.pow n), ih, pow_succ']
    rfl

/-- For `f` with zero constant term and invertible linear coefficient, `f^{∘n}` is the image of
`T` under the `n`-fold iterate of `x ↦ x(f)`. -/
theorem ofPowerSeries_iterate {f : PowerSeries R} (hf : f.constantCoeff = 0)
    (hf' : IsUnit (f.coeff 1)) (n : ℕ) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.iterate f n) =
      (substEquiv f)^[n] (HahnSeries.single (1 : ℤ) 1) := by
  rw [← AlgEquiv.coe_pow, ← substEquiv_iterate hf hf', substEquiv_X
    (PowerSeries.constantCoeff_iterate hf n)
    (by rw [PowerSeries.coeff_one_iterate hf]; exact hf'.pow n)]

/-- The `R`-linear operator `x ↦ x(g) - x` on `R((T))`. For `g = f_σ` it is the operator
`σ - 1` of the proof of Yuan, Lemma 3.3. -/
def substSubOne (g : LaurentSeries R) : Module.End R (LaurentSeries R) where
  toFun x := subst g x - x
  map_add' x y := by
    rw [map_add]
    abel
  map_smul' a x := by
    simp only [← HahnSeries.C_mul_eq_smul, RingHom.id_apply, map_mul, subst_C]
    ring

/-- `substSubOne g x = x(g) - x`. -/
@[simp]
theorem substSubOne_apply (g x : LaurentSeries R) : substSubOne g x = subst g x - x := rfl

/-- Let `g = T + O(T ^ (d + 1))` with `d ≥ 1`. If `x = O(T ^ m)`, `m ∈ ℤ`, then applying
`x ↦ x(g) - x` to `x` `n` times gives `O(T ^ (m + n d))` (Yuan, Lemma 3.2). -/
theorem substSubOne_pow_mem {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) (n : ℕ) {m : ℤ}
    {x : LaurentSeries R} (hx : x ∈ orderAddSubgroup m) :
    (substSubOne g ^ n) x ∈ orderAddSubgroup (m + n * d) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, add_zero] using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, substSubOne_apply,
      show m + ((n + 1 : ℕ) : ℤ) * d = m + n * d + d by push_cast; ring]
    exact subst_sub_mem_orderAddSubgroup hd hg ih

private theorem substSubOne_pow_sub_single_mem {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    {α : R} (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2)) {x : LaurentSeries R} {m : ℤ} {b : R}
    (hx : x - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) (n : ℕ) :
    (substSubOne g ^ n) x - HahnSeries.single (m + n * d)
      (b * ∏ i ∈ Finset.range n, ((m + i * d : ℤ) : R) * α) ∈
        orderAddSubgroup (m + n * d + 1) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, add_zero,
      Finset.range_zero, Finset.prod_empty, mul_one] using hx
  | succ n ih =>
    have hb : b * ∏ i ∈ Finset.range (n + 1), ((m + i * d : ℤ) : R) * α =
        ((m + n * d : ℤ) : R) * α * (b * ∏ i ∈ Finset.range n, ((m + i * d : ℤ) : R) * α) := by
      rw [Finset.prod_range_succ]
      ring
    rw [pow_succ', Module.End.mul_apply, substSubOne_apply,
      show m + ((n + 1 : ℕ) : ℤ) * d = m + n * d + d by push_cast; ring, hb]
    exact subst_sub_leadingTerm_mem hd hg ih

end Subst

section Field

variable {k : Type*} [Field k]

private theorem order_substEquiv_symm {w : PowerSeries k} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) (x : LaurentSeries k) :
    ((substEquiv w).symm x).order = x.order := by
  conv_rhs => rw [← (substEquiv w).apply_symm_apply x]
  exact (order_substEquiv hw hw' _).symm

private theorem orderTop_substEquiv_symm {w : PowerSeries k} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) (x : LaurentSeries k) :
    ((substEquiv w).symm x).orderTop = x.orderTop := by
  conv_rhs => rw [← (substEquiv w).apply_symm_apply x]
  exact (orderTop_substEquiv hw hw' _).symm

/-- In characteristic `p`, the `p`-th power of `x ↦ x(g) - x` is `x ↦ σ^p x - x`, where `σ` is
`x ↦ x(g)`. -/
theorem substSubOne_pow_char_apply (p : ℕ) [Fact p.Prime] [CharP k p] (g x : LaurentSeries k) :
    (substSubOne g ^ p) x = (subst g)^[p] x - x := by
  have : CharP (Module.End k (LaurentSeries k)) p :=
    ((algebraMap k (Module.End k (LaurentSeries k))).charP_iff_charP p).mp inferInstance
  have hS : ⇑(substSubOne g + 1) = subst g := funext fun y ↦ by
    rw [LinearMap.add_apply, substSubOne_apply, Module.End.one_apply, sub_add_cancel]
  have h := sub_pow_char_of_commute p (Commute.one_right (substSubOne g + 1))
  rw [add_sub_cancel_right, one_pow] at h
  rw [h, LinearMap.sub_apply, Module.End.pow_apply, hS, Module.End.one_apply]

private theorem substSubOne_pow_char (p : ℕ) [Fact p.Prime] [CharP k p]
    (g x : LaurentSeries k) : substSubOne g (x ^ p) = substSubOne g x ^ p := by
  have : CharP (LaurentSeries k) p :=
    ((algebraMap k (LaurentSeries k)).charP_iff_charP p).mp inferInstance
  rw [substSubOne_apply, substSubOne_apply, map_pow, sub_pow_char]

/-- For `g = T + O(T ^ (d + 1))`, `d ≥ 1`, and `p ∣ d + 1`, one has
`T ^ (d + 1)(g) - T ^ (d + 1) = O(T ^ ((p + 1) d + 1))`. -/
private theorem substSubOne_single_mem_of_dvd (p : ℕ) [Fact p.Prime] [CharP k p]
    {g : LaurentSeries k} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) (hdp : (p : ℤ) ∣ d + 1)
    (α : k) :
    substSubOne g (HahnSeries.single (d + 1) α) ∈ orderAddSubgroup ((p + 1) * d + 1) := by
  obtain ⟨q, hq⟩ := hdp
  have hmon : HahnSeries.single q (1 : k) ^ p = HahnSeries.single (d + 1) 1 := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, ← hq]
  have hb : substSubOne g (HahnSeries.single q 1) ∈ orderAddSubgroup (q + d) := by
    rw [substSubOne_apply]
    exact subst_sub_mem_orderAddSubgroup hd hg HahnSeries.orderTop_single_le
  have hp := pow_mem_orderAddSubgroup hb p
  rw [← substSubOne_pow_char p, hmon,
    show (p : ℤ) * (q + d) = (p + 1) * d + 1 by linear_combination -hq] at hp
  have hsingle : (HahnSeries.single (d + 1) α : LaurentSeries k) =
      α • HahnSeries.single (d + 1) 1 := by
    rw [← HahnSeries.C_mul_eq_smul]
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hsingle, map_smul]
  exact hp.trans (HahnSeries.orderTop_le_orderTop_smul α _)

private theorem prod_ne_zero_of_resonant (p : ℕ) [Fact p.Prime] [CharP k p] {d ℓ : ℤ}
    (hd : (p : ℤ) ∣ d + 1) (hℓ : (p : ℤ) ∣ ℓ + 1) {α : k} (hα : α ≠ 0) :
    ∏ i ∈ Finset.range (p - 1), ((ℓ + i * d : ℤ) : k) * α ≠ 0 := by
  have hcast (m : ℤ) (hm : (p : ℤ) ∣ m + 1) : (m : k) = -1 := by
    obtain ⟨q, hq⟩ := hm
    have hz : ((m + 1 : ℤ) : k) = 0 := by
      rw [hq, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero k p, zero_mul]
    exact eq_neg_of_add_eq_zero_left (by simpa only [Int.cast_add, Int.cast_one] using hz)
  refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ mul_ne_zero ?_ hα
  have heq : ((ℓ + i * d : ℤ) : k) = -((i + 1 : ℕ) : k) := by
    push_cast
    rw [hcast ℓ hℓ, hcast d hd]
    ring
  rw [heq, neg_ne_zero]
  exact (CharP.cast_eq_zero_iff k p (i + 1)).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hi; omega))

/-- Lemma 3.3 for a Laurent series `g`: `v_T(σ^p T - T) = ℓ + (p - 1) d` for `σ : x ↦ x(g)`. -/
private theorem order_subst_iterate_sub_X_of_resonant (p : ℕ) [Fact p.Prime] [CharP k p]
    {g : LaurentSeries k} {d ℓ : ℤ} (hd : 1 ≤ d) (hlo : d + 2 ≤ ℓ) (hhi : ℓ ≤ 2 * d)
    (hdp : (p : ℤ) ∣ d + 1) (hℓp : (p : ℤ) ∣ ℓ + 1) {α β : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α -
      HahnSeries.single ℓ β ∈ orderAddSubgroup (ℓ + 1)) :
    ((subst g)^[p] (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1).order =
      ℓ + ((p : ℤ) - 1) * d := by
  set N := substSubOne g
  set L := ℓ + ((p : ℤ) - 1) * d
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have hfirst : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2) :=
    orderAddSubgroup_antitone hlo (mem_orderAddSubgroup_of_sub_single_mem hg)
  have hδ : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
    mem_orderAddSubgroup_of_sub_single_mem
      (orderAddSubgroup_antitone (show d + 1 + 1 ≤ d + 2 by omega) hfirst)
  have hA : (N ^ (p - 1)) (HahnSeries.single (d + 1) α) ∈ orderAddSubgroup (L + 1) := by
    have h := substSubOne_pow_mem hd hδ (p - 2) (substSubOne_single_mem_of_dvd p hd hδ hdp α)
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ, Module.End.mul_apply]
    refine orderAddSubgroup_antitone ?_ h
    have hpd : 2 * d ≤ p * d := mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (by omega)
    rw [show ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 by omega]
    linarith
  have hB := substSubOne_pow_sub_single_mem hd hfirst (x := HahnSeries.single ℓ β) (m := ℓ)
    (b := β) (by simp) (p - 1)
  rw [hp1] at hB
  have hE : (N ^ (p - 1)) (g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α -
      HahnSeries.single ℓ β) ∈ orderAddSubgroup (L + 1) := by
    have h := substSubOne_pow_mem hd hδ (p - 1) hg
    rwa [hp1, add_right_comm] at h
  have hinit : N (HahnSeries.single (1 : ℤ) 1) = HahnSeries.single (d + 1) α +
      HahnSeries.single ℓ β + (g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α -
        HahnSeries.single ℓ β) := by
    rw [substSubOne_apply,
      subst_X (isAdmissible_of_sub_X_mem (orderAddSubgroup_antitone (by omega) hδ))]
    abel
  have hres : (N ^ p) (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single L
      (β * ∏ i ∈ Finset.range (p - 1), ((ℓ + i * d : ℤ) : k) * α) ∈
        orderAddSubgroup (L + 1) := by
    rw [show p = p - 1 + 1 by omega, pow_succ, Module.End.mul_apply, hinit, map_add, map_add]
    convert add_mem (add_mem hA hB) hE using 1
    abel
  rw [substSubOne_pow_char_apply] at hres
  exact order_eq_of_sub_single_mem (mul_ne_zero hβ (prod_ne_zero_of_resonant p hdp hℓp hα)) hres

end Field

end LaurentSeries

namespace PowerSeries

open LaurentSeries

section Field

variable {k : Type*} [Field k]

/-- The ramification number does not depend on the uniformizer: for `w` with `w(0) = 0` and
`w'(0) ≠ 0` and every `f` with `f(0) = 0`, the conjugate `w ∘ f ∘ w^{∘-1}` has the same
ramification number as `f` (Yuan, §3.2). -/
theorem ramificationNumber_conj {w f : k⟦X⟧} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) (hf : f.constantCoeff = 0) :
    (conj w f).ramificationNumber = f.ramificationNumber := by
  by_cases hf1 : f.coeff 1 = 1
  swap
  · rw [ramificationNumber_eq_zero hf hf1, ramificationNumber_eq_zero (constantCoeff_conj hw hf)
      (by rwa [coeff_one_conj hw' hf])]
  by_cases hfX : f = X
  · rw [hfX, conj_X_right hw hw']
  have hf' : IsUnit (f.coeff 1) := hf1 ▸ isUnit_one
  have hd := one_le_ramificationNumber_iff.mpr ⟨hfX, hf, hf1⟩
  have hD : (HahnSeries.ofPowerSeries ℤ k (derivative w)).order = 0 := by
    rw [← derivative_ofPowerSeries]
    exact order_derivative_ofPowerSeries hw'
  have hB := order_subst_ofPowerSeries_sub_eq hd (orderTop_ofPowerSeries_sub_X hfX) w
    (by rw [← derivative_ofPowerSeries]; exact (isUnit_derivative_ofPowerSeries w hw').ne_zero)
    (by omega)
  have hsymm : (substEquiv w).symm (HahnSeries.ofPowerSeries ℤ k w) =
      HahnSeries.single (1 : ℤ) 1 :=
    (substEquiv w).symm_apply_eq.mpr (substEquiv_X hw hw').symm
  rw [ramificationNumber, ofPowerSeries_conj hw hw' hf hf', ← hsymm, ← map_sub,
    order_substEquiv_symm hw hw', substEquiv_apply hf hf', hB, hD]
  ring

/-- **Lemma 3.3** (Yuan). Let `k` have characteristic `p`, and let
`f = T + α T ^ (d + 1) + β T ^ ℓ + O(T ^ (ℓ + 1))` with `α, β ≠ 0`, `d ≥ 1`,
`d + 2 ≤ ℓ ≤ 2 d` and `d ≡ ℓ ≡ -1 (mod p)`. Then the `p`-fold composite `f^{∘p}` has
ramification number `ℓ + (p - 1) d - 1`; as `ℓ ≤ 2 d`, this is smaller than `(p + 1) d`. -/
theorem ramificationNumber_iterate_eq_of_resonant (p : ℕ) [Fact p.Prime] [CharP k p]
    {f : k⟦X⟧} {d ℓ : ℤ} (hd : 1 ≤ d) (hlo : d + 2 ≤ ℓ) (hhi : ℓ ≤ 2 * d)
    (hdp : (p : ℤ) ∣ d + 1) (hℓp : (p : ℤ) ∣ ℓ + 1) {α β : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hf : HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α - HahnSeries.single ℓ β ∈ orderAddSubgroup (ℓ + 1)) :
    (iterate f p).ramificationNumber = ℓ + ((p : ℤ) - 1) * d - 1 := by
  have h2 : HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup 2 :=
    orderAddSubgroup_antitone (by omega) (mem_orderAddSubgroup_of_sub_single_mem
      (orderAddSubgroup_antitone (by omega) (mem_orderAddSubgroup_of_sub_single_mem hf)))
  obtain ⟨hf0, hf1⟩ := constantCoeff_eq_zero_and_coeff_one_eq_one h2
  have hf' : IsUnit (f.coeff 1) := hf1 ▸ isUnit_one
  rw [ramificationNumber, ofPowerSeries_iterate hf0 hf',
    show ⇑(substEquiv f) = LaurentSeries.subst (HahnSeries.ofPowerSeries ℤ k f) from
      funext (substEquiv_apply hf0 hf'),
    order_subst_iterate_sub_X_of_resonant p hd hlo hhi hdp hℓp hα hβ hf]

private theorem ofPowerSeries_X_add_monomial (q : ℕ) (t : k) :
    HahnSeries.ofPowerSeries ℤ k (X + monomial q t) =
      HahnSeries.single (1 : ℤ) 1 + HahnSeries.single (q : ℤ) t := by
  rw [map_add, HahnSeries.ofPowerSeries_X]
  congr 1
  ext j
  cases j with
  | ofNat n => simp [coeff_coe, coeff_monomial, HahnSeries.coeff_single]
  | negSucc n =>
    rw [coeff_coe, ite_eq_left (Int.negSucc_lt_zero n), HahnSeries.coeff_single_of_ne (by omega)]

/-- Removal of a nonresonant coefficient: for `g = T + α T ^ (d + 1) + β T ^ (d + q) +
O(T ^ (d + q + 1))` with `p ∣ d + 1` and `p ∤ q`, the coordinate change `w = T + t T ^ q` with a
suitable `t` gives `w ∘ g ∘ w^{∘-1} = T + α T ^ (d + 1) + O(T ^ (d + q + 1))`. -/
private theorem exists_conj_sub_mem (p : ℕ) [Fact p.Prime] [CharP k p] {g : k⟦X⟧}
    (hg0 : g.constantCoeff = 0) (hg1 : g.coeff 1 = 1) {d : ℤ} (hd : 1 ≤ d)
    (hdp : (p : ℤ) ∣ d + 1) {q : ℕ} (hq : 2 ≤ q) (hpq : ¬ p ∣ q) {α β : k} (hα : α ≠ 0)
    (hg : HahnSeries.ofPowerSeries ℤ k g - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α - HahnSeries.single (d + q) β ∈
        orderAddSubgroup (d + q + 1)) :
    ∃ w : k⟦X⟧, w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧
      HahnSeries.ofPowerSeries ℤ k (conj w g) - HahnSeries.single (1 : ℤ) 1 -
        HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + q + 1) := by
  have hdk : ((d + 1 : ℤ) : k) = 0 := by
    obtain ⟨n, hn⟩ := hdp
    rw [hn, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero k p, zero_mul]
  have hqk : (q : k) ≠ 0 := (CharP.cast_eq_zero_iff k p q).not.mpr hpq
  obtain ⟨t, ht⟩ : ∃ t : k, β + (q : k) * α * t = 0 :=
    ⟨-β / ((q : k) * α), by field_simp; ring⟩
  obtain ⟨w, hw⟩ : ∃ w : k⟦X⟧, w = X + monomial q t := ⟨_, rfl⟩
  have hw0 : w.constantCoeff = 0 := by
    rw [hw, map_add, constantCoeff_X, zero_add, ← coeff_zero_eq_constantCoeff_apply,
      coeff_monomial, ite_eq_right_iff]
    exact fun h ↦ absurd h (by omega)
  have hw1 : w.coeff 1 = 1 := by
    simp [hw, coeff_monomial, show (1 : ℕ) ≠ q by omega]
  have hw' : IsUnit (w.coeff 1) := hw1 ▸ isUnit_one
  have hg' : IsUnit (g.coeff 1) := hg1 ▸ isUnit_one
  have hfirst : HahnSeries.ofPowerSeries ℤ k g - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + 2) :=
    orderAddSubgroup_antitone (by omega) (mem_orderAddSubgroup_of_sub_single_mem hg)
  -- `w(g) - w = α T ^ (d + 1) + O(T ^ (d + q + 1))` for `w = T + t T ^ q`
  have hA : LaurentSeries.subst (HahnSeries.ofPowerSeries ℤ k g)
      (HahnSeries.ofPowerSeries ℤ k w) - HahnSeries.ofPowerSeries ℤ k w -
        HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + q + 1) := by
    have hmono := subst_sub_leadingTerm_mem hd hfirst (x := HahnSeries.single (q : ℤ) t)
      (m := q) (b := t) (by simp)
    rw [show (q : ℤ) + d = d + q by ring] at hmono
    convert add_mem hg hmono using 1
    rw [hw, ofPowerSeries_X_add_monomial, map_add,
      LaurentSeries.subst_X (isAdmissible_ofPowerSeries hg0 hg'),
      show ((q : ℤ) : k) * α * t = -β by rw [Int.cast_natCast]; linear_combination ht,
      HahnSeries.single_neg]
    abel
  -- `(T ^ (d + 1))(w) = T ^ (d + 1) + O(T ^ (d + q + 1))`, as `p ∣ d + 1`
  have hEa : substEquiv w (HahnSeries.single (d + 1) α) - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + q + 1) := by
    have hwexp : HahnSeries.ofPowerSeries ℤ k w - HahnSeries.single (1 : ℤ) 1 -
        HahnSeries.single ((q : ℤ) - 1 + 1) t ∈ orderAddSubgroup ((q : ℤ) - 1 + 2) := by
      simp only [hw, ofPowerSeries_X_add_monomial, sub_add_cancel, add_sub_cancel_left,
        sub_self, zero_mem]
    have h := subst_sub_leadingTerm_mem (by omega) hwexp (x := HahnSeries.single (d + 1) α)
      (m := d + 1) (b := α) (by simp)
    rwa [show d + 1 + ((q : ℤ) - 1) = d + q by ring, hdk, zero_mul, zero_mul,
      HahnSeries.single_eq_zero, sub_zero, ← substEquiv_apply hw0 hw'] at h
  have hsymm : (substEquiv w).symm (HahnSeries.ofPowerSeries ℤ k w) =
      HahnSeries.single (1 : ℤ) 1 :=
    (substEquiv w).symm_apply_eq.mpr (substEquiv_X hw0 hw').symm
  refine ⟨w, hw0, hw', ?_⟩
  have hconj : HahnSeries.ofPowerSeries ℤ k (conj w g) - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α = (substEquiv w).symm
        (LaurentSeries.subst (HahnSeries.ofPowerSeries ℤ k g) (HahnSeries.ofPowerSeries ℤ k w) -
          HahnSeries.ofPowerSeries ℤ k w - substEquiv w (HahnSeries.single (d + 1) α)) := by
    rw [map_sub, map_sub, AlgEquiv.symm_apply_apply, hsymm, ofPowerSeries_conj hw0 hw' hg0 hg',
      substEquiv_apply hg0 hg']
  have hmem := sub_mem hA hEa
  rw [sub_sub_sub_cancel_right] at hmem
  rwa [hconj, mem_orderAddSubgroup, orderTop_substEquiv_symm hw0 hw', ← mem_orderAddSubgroup]

/-- **Theorem 3.4** (Yuan). Let `k` have characteristic `p`, and let `f ∈ k⟦T⟧` have
ramification number `d ≡ -1 (mod p)` such that `f^{∘p}` has ramification number at least
`(p + 1) d`. Then there are a uniformizer `w ∈ T k⟦T⟧` (`w(0) = 0`, `w'(0) ≠ 0`) and `α ≠ 0`
with `w ∘ f ∘ w^{∘-1} = T + α T ^ (d + 1) + O(T ^ (2 d + 1))`. -/
theorem exists_normalForm (p : ℕ) [Fact p.Prime] [CharP k p] {f : k⟦X⟧}
    (hdp : (p : ℤ) ∣ f.ramificationNumber + 1)
    (hnext : ((p : ℤ) + 1) * f.ramificationNumber ≤ (iterate f p).ramificationNumber) :
    ∃ w : k⟦X⟧, w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧ ∃ α : k, α ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ k (conj w f) - HahnSeries.single (1 : ℤ) 1 -
        HahnSeries.single (f.ramificationNumber + 1) α ∈
          orderAddSubgroup (2 * f.ramificationNumber + 1) := by
  set d := f.ramificationNumber with hd_def
  obtain hd | hd : d = -1 ∨ 1 ≤ d := by
    have h0 : d ≠ 0 := by
      intro h
      rw [h, zero_add] at hdp
      have h1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdp
      exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast h1)
    have h1 := neg_one_le_ramificationNumber f
    rw [← hd_def] at h1
    omega
  · refine ⟨X, constantCoeff_X, by simp, 1, one_ne_zero, ?_⟩
    rw [hd]
    refine orderAddSubgroup_antitone (show (2 * -1 + 1 : ℤ) ≤ 0 by norm_num)
      (sub_mem (sub_mem (ofPowerSeries_mem_orderAddSubgroup_zero _)
        (orderAddSubgroup_antitone (show (0 : ℤ) ≤ 1 by norm_num)
          HahnSeries.orderTop_single_le)) ?_)
    rw [neg_add_cancel]
    exact HahnSeries.orderTop_single_le
  obtain ⟨hfX, hf0, hf1⟩ := one_le_ramificationNumber_iff.mp hd
  have hf : HasSubst f := .of_constantCoeff_zero' hf0
  have hδ := ofPowerSeries_sub_X_mem_orderAddSubgroup f
  rw [← hd_def] at hδ
  set α := (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).coeff (d + 1)
  have hα : α ≠ 0 := by
    have hne : HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1 ≠ 0 :=
      HahnSeries.orderTop_ne_top.mp (by rw [orderTop_ofPowerSeries_sub_X hfX]; simp)
    have hord : (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).order = d + 1 := by
      rw [hd_def, ramificationNumber, sub_add_cancel]
    simpa only [α, ← hord] using HahnSeries.coeff_order_eq_zero.not.mpr hne
  have hiter {w : k⟦X⟧} (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
      (iterate (conj w f) p).ramificationNumber = (iterate f p).ramificationNumber := by
    rw [← conj_iterate hw hw' hf, ramificationNumber_conj hw hw' (constantCoeff_iterate hf0 p)]
  have aux (n : ℕ) (hn : n ≤ d.toNat - 1) : ∃ w : k⟦X⟧, w.constantCoeff = 0 ∧
      IsUnit (w.coeff 1) ∧ HahnSeries.ofPowerSeries ℤ k (conj w f) -
        HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
          orderAddSubgroup (d + 2 + n) := by
    induction n with
    | zero =>
      refine ⟨X, constantCoeff_X, by simp, ?_⟩
      rw [conj_X hf, Nat.cast_zero, add_zero, show d + 2 = d + 1 + 1 by ring]
      exact sub_single_coeff_mem_orderAddSubgroup hδ
    | succ n ih =>
      obtain ⟨w, hw, hw', hg⟩ := ih (by omega)
      have hg0 : (conj w f).constantCoeff = 0 := constantCoeff_conj hw hf0
      have hg1 : (conj w f).coeff 1 = 1 := (coeff_one_conj hw' hf0).trans hf1
      have htail := sub_single_coeff_mem_orderAddSubgroup hg
      set β := (HahnSeries.ofPowerSeries ℤ k (conj w f) - HahnSeries.single (1 : ℤ) 1 -
        HahnSeries.single (d + 1) α).coeff (d + 2 + n)
      have hidx : d + 2 + n + 1 = d + 2 + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      by_cases hβ : β = 0
      · refine ⟨w, hw, hw', ?_⟩
        rwa [hβ, HahnSeries.single_eq_zero, sub_zero, hidx] at htail
      have hq : d + 2 + n = d + ((n + 2 : ℕ) : ℤ) := by push_cast; ring
      have hpq : ¬ p ∣ n + 2 := by
        intro hpq
        have hℓp : (p : ℤ) ∣ d + 2 + n + 1 := by
          rw [show d + 2 + n + 1 = d + 1 + ((n + 2 : ℕ) : ℤ) by push_cast; ring]
          exact dvd_add hdp (Int.natCast_dvd_natCast.mpr hpq)
        have hr := ramificationNumber_iterate_eq_of_resonant p hd (by omega) (by omega) hdp hℓp
          hα hβ htail
        rw [hiter hw hw'] at hr
        have hn2 : (n : ℤ) + 2 ≤ d := by omega
        linarith
      rw [hq] at htail
      obtain ⟨v, hv, hv', hconj⟩ := exists_conj_sub_mem p hg0 hg1 hd hdp (by omega) hpq hα htail
      refine ⟨v.subst w, ?_, ?_, ?_⟩
      · rw [constantCoeff_subst_of_constantCoeff_zero' hw, hv]
      · rw [coeff_one_subst hw]
        exact hv'.mul hw'
      · rw [← conj_conj hv hv' hw hw' hf, ← hidx, hq]
        exact hconj
  obtain ⟨w, hw, hw', h⟩ := aux (d.toNat - 1) le_rfl
  refine ⟨w, hw, hw', α, hα, ?_⟩
  rwa [show d + 2 + ((d.toNat - 1 : ℕ) : ℤ) = 2 * d + 1 by omega] at h

end Field

end PowerSeries

end NormalForm

/-! ### Growth of the ramification numbers of `p`-power iterates -/

section IterateGrowth

namespace LaurentSeries

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]

/-- If `x ↦ x(P)` has infinite order, then `P(0) = 0` and `P'(0)` is a unit. -/
theorem constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder {P : PowerSeries R}
    (h : ¬ IsOfFinOrder (substEquiv P)) : P.constantCoeff = 0 ∧ IsUnit (P.coeff 1) := by
  by_contra hP
  rw [substEquiv_of_not hP] at h
  exact h IsOfFinOrder.one

end LaurentSeries

namespace PowerSeries

open LaurentSeries Filter

section Subst

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]

/-- If `x ↦ x(f)` has infinite order, then `f^{∘n} ≠ X` for every `n > 0`. -/
theorem iterate_ne_X_of_not_isOfFinOrder {f : R⟦X⟧} (hf : ¬ IsOfFinOrder (substEquiv f))
    {n : ℕ} (hn : 0 < n) : iterate f n ≠ X := by
  obtain ⟨hf0, hf'⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  intro h
  refine hf (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩)
  rw [← substEquiv_iterate hf0 hf', h, ← iterate_zero f, substEquiv_iterate hf0 hf', pow_zero]

/-- If `f = T + O(T ^ 2)` and `σ : x ↦ x(f)` has infinite order, then `f^{∘n}` has positive
ramification number for every `n > 0`. -/
theorem one_le_ramificationNumber_iterate {f : R⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) {n : ℕ} (hn : 0 < n) :
    1 ≤ (iterate f n).ramificationNumber := by
  obtain ⟨hf0, -⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  exact one_le_ramificationNumber_iff.mpr ⟨iterate_ne_X_of_not_isOfFinOrder hf hn,
    constantCoeff_iterate hf0 n, by rw [coeff_one_iterate hf0, hf1, one_pow]⟩

end Subst

section Field

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

private theorem ofPowerSeries_iterate_sub_X_mem {f : k⟦X⟧} (hf : 1 ≤ f.ramificationNumber) :
    HahnSeries.ofPowerSeries ℤ k (iterate f p) - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup (p * f.ramificationNumber + 1) := by
  obtain ⟨-, hf0, hf1⟩ := one_le_ramificationNumber_iff.mp hf
  have hf' : IsUnit (f.coeff 1) := hf1 ▸ isUnit_one
  rw [ofPowerSeries_iterate hf0 hf',
    show ⇑(substEquiv f) = LaurentSeries.subst (HahnSeries.ofPowerSeries ℤ k f) from
      funext (substEquiv_apply hf0 hf'), ← substSubOne_pow_char_apply p, add_comm]
  exact substSubOne_pow_mem hf (ofPowerSeries_sub_X_mem_orderAddSubgroup f) p
    HahnSeries.orderTop_single_le

/-- If `f = T + O(T ^ 2)` has ramification number `d ≥ 1` and `f^{∘p} ≠ X`, then `f^{∘p}` has
ramification number at least `p d`: `i(σ ^ p) ≥ p i(σ)`. -/
theorem mul_ramificationNumber_le_ramificationNumber_iterate {f : k⟦X⟧}
    (hf : 1 ≤ f.ramificationNumber) (hfp : iterate f p ≠ X) :
    (p : ℤ) * f.ramificationNumber ≤ (iterate f p).ramificationNumber :=
  (le_ramificationNumber_iff hfp).mpr (ofPowerSeries_iterate_sub_X_mem p hf)

/-- If `f = T + O(T ^ 2)` and `σ : x ↦ x(f)` has infinite order, then
`i(σ ^ (p ^ (n + 1))) ≥ p i(σ ^ (p ^ n))`. -/
theorem mul_ramificationNumber_iterate_pow_le {f : k⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) (n : ℕ) :
    (p : ℤ) * (iterate f (p ^ n)).ramificationNumber ≤
      (iterate f (p ^ (n + 1))).ramificationNumber := by
  obtain ⟨hf0, -⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  have hp := (Fact.out : p.Prime).pos
  have hne := iterate_ne_X_of_not_isOfFinOrder hf (pow_pos hp (n + 1))
  rw [pow_succ, iterate_mul (.of_constantCoeff_zero' hf0)] at hne ⊢
  exact mul_ramificationNumber_le_ramificationNumber_iterate p
    (one_le_ramificationNumber_iterate hf1 hf (pow_pos hp n)) hne

/-- If `f = T + O(T ^ 2)` and `σ : x ↦ x(f)` has infinite order, then the ramification numbers
`i(σ ^ (p ^ n))` strictly increase (Yuan, proof of Lemma 4.2). -/
theorem strictMono_ramificationNumber_iterate_pow {f : k⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) :
    StrictMono fun n : ℕ ↦ (iterate f (p ^ n)).ramificationNumber := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h := mul_ramificationNumber_iterate_pow_le p hf1 hf n
  have h1 := one_le_ramificationNumber_iterate hf1 hf (pow_pos (Fact.out : p.Prime).pos n)
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h0 : (0 : ℤ) ≤ (iterate f (p ^ n)).ramificationNumber := by omega
  linarith [mul_le_mul_of_nonneg_right hp h0]

/-- If `f = T + O(T ^ 2)` and `σ : x ↦ x(f)` has infinite order, then the ramification numbers
`i(σ ^ (p ^ n))` tend to infinity (Yuan, proof of Lemma 4.2). -/
theorem tendsto_ramificationNumber_iterate_pow_atTop {f : k⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) :
    Tendsto (fun n : ℕ ↦ (iterate f (p ^ n)).ramificationNumber) atTop atTop := by
  have hmono := strictMono_ramificationNumber_iterate_pow p hf1 hf
  have hlow (n : ℕ) : (n : ℤ) ≤ (iterate f (p ^ n)).ramificationNumber := by
    induction n with
    | zero =>
      have := one_le_ramificationNumber_iterate hf1 hf (pow_pos (Fact.out : p.Prime).pos 0)
      push_cast
      omega
    | succ n ih =>
      have h : (iterate f (p ^ n)).ramificationNumber <
          (iterate f (p ^ (n + 1))).ramificationNumber := hmono (Nat.lt_succ_self n)
      push_cast
      omega
  exact tendsto_atTop_atTop_of_monotone hmono.monotone fun b ↦ ⟨b.toNat, by
    have := hlow b.toNat
    omega⟩

end Field

end PowerSeries

end IterateGrowth
