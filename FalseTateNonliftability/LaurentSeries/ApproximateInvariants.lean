/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.PowerSeries.UnitCompactness
public import FalseTateNonliftability.PowerSeries.UnitRigidity

/-!
# Valuations of approximate invariants

Let `κ` be a finite field of characteristic `p`, let `f ∈ T + T ^ 2 κ⟦T⟧` be such that the
automorphism `σ : x ↦ x(f)` of `κ((T))` has infinite order, and let `x_n ∈ κ((T))ˣ` be
approximate invariants of `σ`: `v_T(σ(x_n) - x_n) - v_T(x_n) → ∞`. If the integers `v_T(x_n)`
converge in `ℤ_p` to `m`, then `m = 0`. Writing `x_n = T ^ (m_n) U_n` with `U_n ∈ κ⟦T⟧ˣ`, one has
`σ(x_n) - x_n = T ^ (m_n) ((f / T) ^ (m_n) U_n(f) - U_n)`, and a limit point `U` of the `U_n`
satisfies `(f / T) ^ m U(f) = U`.

## Main results

* `LaurentSeries.padic_limit_order_eq_zero_of_approximate_invariance`: Yuan, Lemma 4.2.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.2.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped PowerSeries.WithPiTopology

namespace LaurentSeries

variable {κ : Type*} [Field κ]

private theorem mem_orderAddSubgroup_of_single_mul_mem {m d : ℤ} {z : LaurentSeries κ}
    (h : HahnSeries.single m 1 * z ∈ orderAddSubgroup (m + d)) : z ∈ orderAddSubgroup d := by
  rw [mem_orderAddSubgroup_iff_coeff] at h ⊢
  intro j hj
  simpa only [HahnSeries.coeff_single_mul, one_mul, add_sub_cancel_left] using h (m + j) (by omega)

/-- For `u ∈ κ⟦T⟧ˣ` and `x = T ^ m P` with `m = v_T(x)`, `x(T u) - x = T ^ m (u ^ m P(T u) - P)`. -/
private theorem subst_X_mul_sub_eq (u : (PowerSeries κ)ˣ) (x : LaurentSeries κ) :
    subst (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ κ (u : PowerSeries κ)) x - x =
      HahnSeries.single x.order 1 * HahnSeries.ofPowerSeries ℤ κ
        (((u ^ x.order : (PowerSeries κ)ˣ) : PowerSeries κ) *
          x.powerSeriesPart.subst (PowerSeries.X * (u : PowerSeries κ)) - x.powerSeriesPart) := by
  have hG := isAdmissible_X_mul_ofPowerSeries u
  rw [← HahnSeries.ofPowerSeries_X, ← map_mul] at hG
  have hP := subst_ofPowerSeries (by simp) hG x.powerSeriesPart
  rw [map_mul, HahnSeries.ofPowerSeries_X] at hP
  conv_lhs => rw [← single_order_mul_powerSeriesPart x]
  rw [map_mul, subst_X_mul_ofPowerSeries_single, hP, map_sub, map_mul]
  ring

/-- **Valuations of approximate invariants** (Yuan, Lemma 4.2). Let `κ` be a finite field of
characteristic `p` and `f = T + O(T ^ 2)` such that `σ : x ↦ x(f)` has infinite order. If
`x_n ∈ κ((T))ˣ` satisfy `v_T(σ(x_n) - x_n) - v_T(x_n) → ∞` and the integers `v_T(x_n)` converge
in `ℤ_p` to `c`, then `c = 0`. -/
theorem padic_limit_order_eq_zero_of_approximate_invariance [Finite κ] (p : ℕ) [Fact p.Prime]
    [CharP κ p] {f : PowerSeries κ} (hf1 : f.coeff 1 = 1) (hf : ¬ IsOfFinOrder (substEquiv f))
    {x : ℕ → LaurentSeries κ} (hx : ∀ n, x n ≠ 0) {c : ℤ_[p]}
    (hc : Tendsto (fun n ↦ ((x n).order : ℤ_[p])) atTop (𝓝 c))
    (happrox : ∀ d : ℤ, ∀ᶠ n in atTop,
      substEquiv f (x n) - x n ∈ orderAddSubgroup ((x n).order + d)) :
    c = 0 := by
  let : TopologicalSpace κ := ⊥
  have : DiscreteTopology κ := ⟨rfl⟩
  obtain ⟨hf0, hf'⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  have hq := PowerSeries.constantCoeff_divXPowOrder_of_tangent hf0 hf1
  obtain ⟨u, hu⟩ : IsUnit f.divXPowOrder :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (hq ▸ isUnit_one)
  have hXu : PowerSeries.X * (u : PowerSeries κ) = f := by
    rw [hu, PowerSeries.X_mul_divXPowOrder_of_tangent hf0 hf1]
  have hdiff (y : LaurentSeries κ) : substEquiv f y - y = HahnSeries.single y.order 1 *
      HahnSeries.ofPowerSeries ℤ κ (((u ^ y.order : (PowerSeries κ)ˣ) : PowerSeries κ) *
        y.powerSeriesPart.subst f - y.powerSeriesPart) := by
    rw [substEquiv_apply hf0 hf', ← hXu, map_mul, HahnSeries.ofPowerSeries_X, subst_X_mul_sub_eq]
  obtain ⟨V, φ, hφ, hconv, -⟩ := exists_subseq_powerSeriesPart_tendsto x hx
  have hlim := PowerSeries.tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto u (hu ▸ hq)
    (a := fun n ↦ (x (φ n)).order) (hc.comp hφ.tendsto_atTop) hconv hf0
  have hzero : Tendsto (fun n ↦ ((u ^ (x (φ n)).order : (PowerSeries κ)ˣ) : PowerSeries κ) *
      (x (φ n)).powerSeriesPart.subst f - (x (φ n)).powerSeriesPart) atTop (𝓝 0) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    rw [map_zero]
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [hφ.tendsto_atTop.eventually (happrox (k + 1))] with n hn
    rw [hdiff] at hn
    simpa only [HahnSeries.ofPowerSeries_apply_coeff] using
      (mem_orderAddSubgroup_iff_coeff _ _).mp (mem_orderAddSubgroup_of_single_mul_mem hn) k
        (by omega)
  refine PowerSeries.eq_zero_of_principalUnitPow_mul_subst_eq hf1 hf V.isUnit ?_
  rw [← hu]
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hzero)

end LaurentSeries
