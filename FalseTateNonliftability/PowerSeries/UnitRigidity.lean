/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.PowerSeries.PrincipalUnits
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Rigidity of the unit identity `(f / T) ^ m (U ∘ f) = U`

Let `κ` be a perfect field of characteristic `p`, let `f ∈ T + T ^ 2 κ⟦T⟧` be such that the
automorphism `σ : x ↦ x(f)` of `κ((T))` has infinite order, and let `U ∈ κ⟦T⟧ˣ`. If `m ∈ ℤ_p`
satisfies `(f / T) ^ m (U ∘ f) = U`, then `(f^{∘n} / T) ^ m (U ∘ f^{∘n}) = U` for every `n`,
and `m = 0`. Here `f / T` is `PowerSeries.divXPowOrder f`, and the power `z ^ m` of the principal
unit `z = f / T` is `PowerSeries.principalUnitPow z m`.

## Main results

* `PowerSeries.principalUnitPow_mul_subst_iterate_eq`: `(f^{∘n} / T) ^ m (U ∘ f^{∘n}) = U`.
* `PowerSeries.exists_pow_eq_of_derivative_eq_zero`: over a perfect field of characteristic `p`,
  a power series with zero derivative is a `p`-th power.
* `PowerSeries.eq_zero_of_principalUnitPow_mul_subst_eq`: `(f / T) ^ m (U ∘ f) = U` implies
  `m = 0`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  proof of Lemma 4.2, equations (4.4) and (4.5).
-/

@[expose] public section

noncomputable section

namespace PowerSeries

open LaurentSeries Filter

section Tangent

variable {R : Type*} [Semiring R] [Nontrivial R] {f : R⟦X⟧}

private theorem order_eq_one_of_tangent (hf : f.constantCoeff = 0) (hf1 : f.coeff 1 = 1) :
    f.order = 1 := by
  refine order_eq_nat.mpr ⟨by rw [hf1]; exact one_ne_zero, fun n hn ↦ ?_⟩
  obtain rfl : n = 0 := by omega
  rwa [coeff_zero_eq_constantCoeff_apply]

/-- If `f = T + O(T ^ 2)`, then `f = T (f / T)`. -/
theorem X_mul_divXPowOrder_of_tangent (hf : f.constantCoeff = 0) (hf1 : f.coeff 1 = 1) :
    X * f.divXPowOrder = f := by
  simpa only [order_eq_one_of_tangent hf hf1, ENat.toNat_one, pow_one] using
    X_pow_order_mul_divXPowOrder (f := f)

/-- If `f = T + O(T ^ 2)`, then `f / T` is a principal unit. -/
theorem constantCoeff_divXPowOrder_of_tangent (hf : f.constantCoeff = 0) (hf1 : f.coeff 1 = 1) :
    f.divXPowOrder.constantCoeff = 1 := by
  rw [constantCoeff_divXPowOrder, order_eq_one_of_tangent hf hf1, ENat.toNat_one, hf1]

end Tangent

section Field

variable {κ : Type*} [Field κ] {p : ℕ} [Fact p.Prime] [CharP κ p]

private theorem divXPowOrder_iterate_succ {f : κ⟦X⟧} (hf : f.constantCoeff = 0)
    (hf1 : f.coeff 1 = 1) (n : ℕ) :
    (iterate f (n + 1)).divXPowOrder = f.divXPowOrder * (iterate f n).divXPowOrder.subst f := by
  have hn1 (n : ℕ) : (iterate f n).coeff 1 = 1 := by rw [coeff_one_iterate hf, hf1, one_pow]
  apply mul_left_cancel₀ (X_ne_zero : (X : κ⟦X⟧) ≠ 0)
  rw [X_mul_divXPowOrder_of_tangent (constantCoeff_iterate hf _) (hn1 _), iterate_succ,
    ← mul_assoc, X_mul_divXPowOrder_of_tangent hf hf1]
  conv_lhs => rw [← X_mul_divXPowOrder_of_tangent (constantCoeff_iterate hf n) (hn1 n)]
  rw [subst_mul (.of_constantCoeff_zero' hf), subst_X (.of_constantCoeff_zero' hf)]

/-- If `f = T + O(T ^ 2)` and `(f / T) ^ m (U ∘ f) = U`, then `(f^{∘n} / T) ^ m (U ∘ f^{∘n}) = U`
for every `n` (Yuan, proof of Lemma 4.2, (4.5)). -/
theorem principalUnitPow_mul_subst_iterate_eq {f U : κ⟦X⟧} (hf : f.constantCoeff = 0)
    (hf1 : f.coeff 1 = 1) {m : ℤ_[p]} (h : principalUnitPow f.divXPowOrder m * U.subst f = U)
    (n : ℕ) : principalUnitPow (iterate f n).divXPowOrder m * U.subst (iterate f n) = U := by
  have hfs : HasSubst f := .of_constantCoeff_zero' hf
  induction n with
  | zero => simp only [iterate_zero, divXPowOrder_X, principalUnitPow_one_base, one_mul, X_subst]
  | succ n ih =>
    have hq : (iterate f n).divXPowOrder.constantCoeff = 1 :=
      constantCoeff_divXPowOrder_of_tangent (constantCoeff_iterate hf n)
        (by rw [coeff_one_iterate hf, hf1, one_pow])
    have hqf : constantCoeff ((iterate f n).divXPowOrder.subst f) = 1 := by
      rw [constantCoeff_subst_of_constantCoeff_zero' hf, hq]
    have ih' := congrArg (fun V : κ⟦X⟧ ↦ V.subst f) ih
    rw [subst_mul hfs, principalUnitPow_subst hq hf, subst_comp_subst_apply (hfs.iterate n) hfs,
      ← iterate_succ] at ih'
    rw [divXPowOrder_iterate_succ hf hf1,
      principalUnitPow_mul_base (constantCoeff_divXPowOrder_of_tangent hf hf1) hqf, mul_assoc, ih',
      h]

variable (p) in
/-- Over a perfect field of characteristic `p`, a power series with zero derivative is a `p`-th
power. -/
theorem exists_pow_eq_of_derivative_eq_zero [PerfectRing κ p] {U : κ⟦X⟧}
    (hU : derivative U = 0) : ∃ V : κ⟦X⟧, V ^ p = U := by
  have hp := (Fact.out : p.Prime)
  refine ⟨mk fun n ↦ (frobeniusEquiv κ p).symm (coeff (p * n) U), ?_⟩
  rw [← map_frobenius_expand p hp.ne_zero]
  ext n
  rw [coeff_map, coeff_expand]
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left k hp.pos, coeff_mk, frobenius_apply_frobeniusEquiv_symm]
  · rw [map_zero]
    obtain _ | n := n
    · exact absurd (dvd_zero p) hn
    have hc := congrArg (coeff n) hU
    rw [coeff_derivative, map_zero, mul_eq_zero] at hc
    refine (hc.resolve_right fun h0 ↦ hn ?_).symm
    exact (CharP.cast_eq_zero_iff κ p (n + 1)).mp (by exact_mod_cast h0)

private theorem order_ofPowerSeries (z : κ⟦X⟧) :
    (HahnSeries.ofPowerSeries ℤ κ z).order = (z.order.toNat : ℤ) := by
  by_cases hz : z = 0
  · simp [hz]
  have he : HahnSeries.ofPowerSeries ℤ κ z ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hz
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero he, HahnSeries.orderTop_ofPowerSeries,
    ← coe_toNat_order hz]
  rfl

/-- If `f = T + O(T ^ 2)`, `f ≠ T`, `U` is a unit, `u ∈ ℤ_p` is a unit and
`(f / T) ^ (u p ^ r) (U ∘ f) = U`, then `v_T(U ∘ f - U) = p ^ r i(f)`. -/
private theorem orderTop_ofPowerSeries_subst_sub {f U : κ⟦X⟧} (hf : f.constantCoeff = 0)
    (hf1 : f.coeff 1 = 1) (hfX : f ≠ X) (hU : IsUnit U) (u : ℤ_[p]ˣ) (r : ℕ)
    (h : principalUnitPow f.divXPowOrder ((u : ℤ_[p]) * (p : ℤ_[p]) ^ r) * U.subst f = U) :
    (HahnSeries.ofPowerSeries ℤ κ (U.subst f - U)).orderTop =
      (((p : ℤ) ^ r * f.ramificationNumber : ℤ) : WithTop ℤ) := by
  have hq := constantCoeff_divXPowOrder_of_tangent hf hf1
  have hfX' : f - X = X * (f.divXPowOrder - 1) := by
    rw [mul_sub, X_mul_divXPowOrder_of_tangent hf hf1, mul_one]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (f.divXPowOrder - 1).order = n := by
    refine ⟨_, (coe_toNat_order fun h0 ↦ hfX ?_).symm⟩
    rw [← sub_eq_zero, hfX', h0, mul_zero]
  have hd : f.ramificationNumber = n := by
    rw [ramificationNumber, ← HahnSeries.ofPowerSeries_X, ← map_sub, order_ofPowerSeries, hfX',
      order_mul, order_X, hn, ← Nat.cast_one, ← Nat.cast_add, ENat.toNat_natCast]
    push_cast
    ring
  have hUf : IsUnit (U.subst f : κ⟦X⟧) := by
    rw [isUnit_iff_constantCoeff, constantCoeff_subst_of_constantCoeff_zero' hf]
    exact isUnit_iff_constantCoeff.mp hU
  have hdiff : U.subst f - U =
      -(principalUnitPow f.divXPowOrder ((u : ℤ_[p]) * (p : ℤ_[p]) ^ r) - 1) * U.subst f := by
    linear_combination h
  have hord : order (U.subst f - U) = ((p ^ r * n : ℕ) : ℕ∞) := by
    rw [hdiff, order_mul, order_neg, order_zero_of_isUnit hUf, add_zero, ← Nat.cast_pow,
      principalUnitPow_mul_natCast hq, order_pow_prime_pow_sub_one,
      order_principalUnitPow_sub_one_of_isUnit hq u.isUnit, hn]
    push_cast
    rfl
  have hne : U.subst f - U ≠ 0 := fun h0 ↦ by
    rw [h0, order_zero] at hord
    exact ENat.top_ne_natCast _ hord
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero
      ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hne),
    order_ofPowerSeries, hord, ENat.toNat_natCast, hd]
  push_cast
  rfl

/-- If `f = T + O(T ^ 2)`, `σ : x ↦ x(f)` has infinite order, `U` is a unit, `u ∈ ℤ_p` is a unit
and `(f / T) ^ (u p ^ (r + 1)) (U ∘ f) = U`, then `U' = 0`. -/
private theorem derivative_eq_zero_of_principalUnitPow_mul_subst_eq {f U : κ⟦X⟧}
    (hf1 : f.coeff 1 = 1) (hf : ¬ IsOfFinOrder (substEquiv f)) (hU : IsUnit U) (u : ℤ_[p]ˣ)
    (r : ℕ)
    (h : principalUnitPow f.divXPowOrder ((u : ℤ_[p]) * (p : ℤ_[p]) ^ (r + 1)) * U.subst f = U) :
    derivative U = 0 := by
  obtain ⟨hf0, -⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  by_contra hD
  have hDe : HahnSeries.ofPowerSeries ℤ κ (derivative U) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hD
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 (tendsto_ramificationNumber_iterate_pow_atTop p hf1 hf)
    ((HahnSeries.ofPowerSeries ℤ κ (derivative U)).order + 2)).exists
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hg0 := constantCoeff_iterate hf0 (p ^ n)
  have hg1 : (iterate f (p ^ n)).coeff 1 = 1 := by rw [coeff_one_iterate hf0, hf1, one_pow]
  have hgX := iterate_ne_X_of_not_isOfFinOrder hf hpn
  have hd := one_le_ramificationNumber_iterate hf1 hf hpn
  have hT := order_subst_ofPowerSeries_sub_eq hd (orderTop_ofPowerSeries_sub_X hgX) U hDe
    (by omega)
  rw [subst_ofPowerSeries hg0 (isAdmissible_ofPowerSeries hg0 (by rw [hg1]; exact isUnit_one)),
    ← map_sub] at hT
  have hB := orderTop_ofPowerSeries_subst_sub hg0 hg1 hgX hU u (r + 1)
    (principalUnitPow_mul_subst_iterate_eq hf0 hf1 h (p ^ n))
  have hne : HahnSeries.ofPowerSeries ℤ κ (U.subst (iterate f (p ^ n)) - U) ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [hB]; exact WithTop.coe_ne_top)
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_inj, hT] at hB
  have hp : (2 : ℤ) ≤ (p : ℤ) ^ (r + 1) :=
    (by exact_mod_cast (Fact.out : p.Prime).two_le : (2 : ℤ) ≤ p).trans
      (le_self_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) (by omega))
  have hd0 : (0 : ℤ) ≤ (iterate f (p ^ n)).ramificationNumber := by omega
  linarith [mul_le_mul_of_nonneg_right hp hd0]

private theorem principalUnitPow_mul_subst_ne [PerfectRing κ p] {f : κ⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) (u : ℤ_[p]ˣ) (r : ℕ) {U : κ⟦X⟧} (hU : IsUnit U) :
    principalUnitPow f.divXPowOrder ((u : ℤ_[p]) * (p : ℤ_[p]) ^ r) * U.subst f ≠ U := by
  obtain ⟨hf0, -⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  have hfs : HasSubst f := .of_constantCoeff_zero' hf0
  induction r generalizing U with
  | zero =>
    intro h
    have hfX : f ≠ X := by
      simpa only [iterate_one hfs] using iterate_ne_X_of_not_isOfFinOrder hf one_pos
    have hmem := subst_ofPowerSeries_sub_mem
      (one_le_ramificationNumber_iff.mpr ⟨hfX, hf0, hf1⟩)
      (ofPowerSeries_sub_X_mem_orderAddSubgroup f) U
    rw [subst_ofPowerSeries hf0 (isAdmissible_ofPowerSeries hf0 (by rw [hf1]; exact isUnit_one)),
      ← map_sub, mem_orderAddSubgroup, orderTop_ofPowerSeries_subst_sub hf0 hf1 hfX hU u 0 h,
      WithTop.coe_le_coe, pow_zero, one_mul] at hmem
    omega
  | succ r ih =>
    intro h
    obtain ⟨V, hV⟩ := exists_pow_eq_of_derivative_eq_zero p
      (derivative_eq_zero_of_principalUnitPow_mul_subst_eq hf1 hf hU u r h)
    have : CharP κ⟦X⟧ p := charP_of_injective_ringHom C_injective p
    refine ih ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp (hV ▸ hU))
      (frobenius_inj κ⟦X⟧ p ?_)
    rw [frobenius_def, frobenius_def, mul_pow,
      ← principalUnitPow_mul_natCast (constantCoeff_divXPowOrder_of_tangent hf0 hf1),
      ← subst_pow hfs, hV, mul_assoc, ← pow_succ]
    exact h

/-- Let `κ` be a perfect field of characteristic `p` and `f = T + O(T ^ 2)` such that
`σ : x ↦ x(f)` has infinite order. If `U ∈ κ⟦T⟧ˣ` and `m ∈ ℤ_p` satisfy
`(f / T) ^ m (U ∘ f) = U`, then `m = 0` (Yuan, proof of Lemma 4.2). -/
theorem eq_zero_of_principalUnitPow_mul_subst_eq [PerfectRing κ p] {f : κ⟦X⟧}
    (hf1 : f.coeff 1 = 1) (hf : ¬ IsOfFinOrder (substEquiv f)) {U : κ⟦X⟧} (hU : IsUnit U)
    {m : ℤ_[p]} (h : principalUnitPow f.divXPowOrder m * U.subst f = U) : m = 0 := by
  by_contra hm
  rw [PadicInt.unitCoeff_spec hm] at h
  exact principalUnitPow_mul_subst_ne hf1 hf _ _ hU h

end Field

end PowerSeries
