/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Differential.ApproximateInvariants
public import FalseTateNonliftability.Mathlib.NumberTheory.Padics.Continuity
public import FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Derivative

/-!
# The `p`-adic limit of ramification numbers and invariant exact differentials

Let `κ` be a finite field of characteristic `p` and let `f ∈ T + T ^ 2 κ⟦T⟧` be such that the
automorphism `σ : x ↦ x(f)` of `κ((T))` has infinite order. Suppose that the ramification numbers
`d_n = i(σ ^ (p ^ n))` converge in `ℤ_p` to `b`. If `σ` fixes a nonzero exact differential
`ω = a dT`, that is, `a(f) f' = a` and `a = U'` for some `U ∈ κ((T))`, then
`b = -v_T(a) - 1 ∈ ℤ`.

If `p ∤ v_T(U)`, then `σ(U) - U = B ^ p` for some `B`, and the orbit sums
`x_n = ∑_{j < p ^ n} σ ^ j (B)` satisfy `x_n ^ p = σ ^ (p ^ n) (U) - U` and
`σ(x_n) - x_n = σ ^ (p ^ n) (B) - B`; they are approximate invariants of `σ` with
`p v_T(x_n) = v_T(U) + d_n`.

## Main results

* `LaurentSeries.padic_ramification_limit_eq_of_invariant_exact_differential`: Yuan,
  Proposition 4.3.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Proposition 4.3.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace LaurentSeries

variable {κ : Type*} [Field κ]

/-- `∑_{j < N} σ ^ j (σ(A) - A) = σ ^ N (A) - A`. -/
private theorem sum_pow_apply_sub (E : LaurentSeries κ ≃ₐ[κ] LaurentSeries κ)
    (A : LaurentSeries κ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (E ^ j) (E A - A) = (E ^ N) A - A := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
    abel

/-- The orbit sum `x = ∑_{j < N} σ ^ j (B)` satisfies `σ(x) - x = σ ^ N (B) - B`. -/
private theorem apply_sum_pow_sub (E : LaurentSeries κ ≃ₐ[κ] LaurentSeries κ)
    (B : LaurentSeries κ) (N : ℕ) :
    E (∑ j ∈ Finset.range N, (E ^ j) B) - ∑ j ∈ Finset.range N, (E ^ j) B = (E ^ N) B - B := by
  rw [← sum_pow_apply_sub, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sub, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ', pow_succ]

/-- In characteristic `p`, if `B ^ p = σ(A) - A`, then
`(∑_{j < N} σ ^ j (B)) ^ p = σ ^ N (A) - A`. -/
private theorem sum_pow_apply_pow_char (p : ℕ) [Fact p.Prime] [CharP κ p]
    (E : LaurentSeries κ ≃ₐ[κ] LaurentSeries κ) {A B : LaurentSeries κ} (hB : B ^ p = E A - A)
    (N : ℕ) : (∑ j ∈ Finset.range N, (E ^ j) B) ^ p = (E ^ N) A - A := by
  have : CharP (LaurentSeries κ) p :=
    ((algebraMap κ (LaurentSeries κ)).charP_iff_charP p).mp inferInstance
  rw [sum_pow_char]
  simp only [← map_pow, hB, sum_pow_apply_sub]

/-- Let `κ` have characteristic `p` and let `g = T + O(T ^ 2)` have ramification number
`d ≥ 1`. If `A ≠ 0` and `p ∤ v_T(A)`, then `A(g) - A ≠ 0` has order `v_T(A) + d`. -/
private theorem ne_zero_and_order_substEquiv_sub (p : ℕ) [CharP κ p] {g : PowerSeries κ}
    (hg : 1 ≤ g.ramificationNumber) {A : LaurentSeries κ} (hA : A ≠ 0)
    (hpA : ¬ (p : ℤ) ∣ A.order) :
    substEquiv g A - A ≠ 0 ∧ (substEquiv g A - A).order = A.order + g.ramificationNumber := by
  obtain ⟨hgX, hg0, hg1⟩ := PowerSeries.one_le_ramificationNumber_iff.mp hg
  set δ := HahnSeries.ofPowerSeries ℤ κ g - HahnSeries.single (1 : ℤ) 1 with hδdef
  have htop := PowerSeries.orderTop_ofPowerSeries_sub_X hgX
  rw [← hδdef] at htop
  have hδ : δ ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [htop]; exact WithTop.coe_ne_top)
  have hδo : δ.order = g.ramificationNumber + 1 :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hδ).trans htop)
  have hα : δ.coeff δ.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hδ
  have htail : HahnSeries.ofPowerSeries ℤ κ g - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (g.ramificationNumber + 1) (δ.coeff δ.order) ∈
        orderAddSubgroup (g.ramificationNumber + 2) := by
    simpa only [← hδdef, hδo, add_assoc, one_add_one_eq_two] using
      sub_leadingTerm_mem_orderAddSubgroup δ
  have hb : (A.order : κ) * δ.coeff δ.order * A.coeff A.order ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mt (CharP.intCast_eq_zero_iff κ p A.order).mp hpA) hα)
      (HahnSeries.coeff_order_eq_zero.not.mpr hA)
  have hmem := subst_sub_leadingTerm_mem hg htail (sub_leadingTerm_mem_orderAddSubgroup A)
  rw [← substEquiv_apply hg0 (hg1 ▸ isUnit_one)] at hmem
  have hc := (mem_orderAddSubgroup_iff_coeff _ _).mp hmem (A.order + g.ramificationNumber)
    (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  exact ⟨HahnSeries.ne_zero_of_coeff_ne_zero (hc ▸ hb), order_eq_of_sub_single_mem hb hmem⟩

/-- **Integrality constraint for invariant exact differentials** (Yuan, Proposition 4.3). Let `κ`
be a finite field of characteristic `p` and `f = T + O(T ^ 2)` such that `σ : x ↦ x(f)` has
infinite order, and suppose that the ramification numbers `i(σ ^ (p ^ n))` converge in `ℤ_p` to
`b`. If `σ` fixes a nonzero exact differential `ω = a dT`, that is, `a = U'` for some `U` and
`a(f) f' = a`, then `b = -v_T(a) - 1`. -/
theorem padic_ramification_limit_eq_of_invariant_exact_differential [Finite κ] (p : ℕ)
    [Fact p.Prime] [CharP κ p] {f : PowerSeries κ} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) {b : ℤ_[p]}
    (hlimit : Tendsto (fun n : ℕ ↦ ((PowerSeries.iterate f (p ^ n)).ramificationNumber : ℤ_[p]))
      atTop (𝓝 b))
    {a : LaurentSeries κ} (ha : a ≠ 0) (hexact : ∃ U : LaurentSeries κ, derivative κ U = a)
    (hinv : substEquiv f a * derivative κ (HahnSeries.ofPowerSeries ℤ κ f) = a) :
    b = -((a.order + 1 : ℤ) : ℤ_[p]) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨hf0, hf'⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  obtain ⟨U, rfl⟩ := hexact
  set A := coefficientPrimitive (derivative κ U)
  have hAd : derivative κ A = derivative κ U := derivative_coefficientPrimitive_derivative U
  have hA : A ≠ 0 := fun h0 ↦ ha (by rw [← hAd, h0, map_zero])
  have hpA : ¬ (p : ℤ) ∣ A.order := not_dvd_order_coefficientPrimitive_derivative p U ha
  obtain ⟨B, hB⟩ := (derivative_eq_zero_iff_exists_pow p (substEquiv f A - A)).mp (by
    rw [map_sub, derivative_substEquiv hf0 hf', hAd, hinv, sub_self])
  set d : ℕ → ℤ := fun n ↦ (PowerSeries.iterate f (p ^ n)).ramificationNumber
  set x : ℕ → LaurentSeries κ := fun n ↦ ∑ j ∈ Finset.range (p ^ n), (substEquiv f ^ j) B
    with hxdef
  have hd (n : ℕ) : 1 ≤ d n :=
    PowerSeries.one_le_ramificationNumber_iterate hf1 hf (pow_pos hp.pos n)
  have hσ (n : ℕ) : substEquiv f ^ (p ^ n) = substEquiv (PowerSeries.iterate f (p ^ n)) :=
    (substEquiv_iterate hf0 hf' _).symm
  have hxo (n : ℕ) : x n ≠ 0 ∧ (p : ℤ) * (x n).order = A.order + d n := by
    have hxp : x n ^ p = substEquiv (PowerSeries.iterate f (p ^ n)) A - A := by
      rw [hxdef, sum_pow_apply_pow_char p _ hB, hσ]
    obtain ⟨hne, ho⟩ := ne_zero_and_order_substEquiv_sub p (hd n) hA hpA
    rw [← hxp] at hne ho
    refine ⟨fun h0 ↦ hne (by rw [h0, zero_pow hp.ne_zero]), ?_⟩
    rw [HahnSeries.order_pow, nsmul_eq_mul] at ho
    exact ho
  have happrox (N : ℤ) : ∀ᶠ n in atTop,
      substEquiv f (x n) - x n ∈ orderAddSubgroup ((x n).order + N) := by
    filter_upwards [tendsto_atTop.mp (PowerSeries.tendsto_ramificationNumber_iterate_pow_atTop
      p hf1 hf) (A.order + p * (N - B.order))] with n hn
    have hg := PowerSeries.one_le_ramificationNumber_iff.mp (hd n)
    have hmem := subst_sub_mem_orderAddSubgroup (hd n)
      (PowerSeries.ofPowerSeries_sub_X_mem_orderAddSubgroup _) (mem_orderAddSubgroup_order B)
    rw [← substEquiv_apply hg.2.1 (hg.2.2 ▸ isUnit_one), ← hσ, ← apply_sum_pow_sub] at hmem
    refine orderAddSubgroup_antitone ?_ hmem
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hdn : d n ≤ (p - 1) * d n := le_mul_of_one_le_left (by linarith [hd n]) (by linarith)
    have h2 : (p : ℤ) * ((x n).order + N) ≤ p * (B.order + d n) := by
      linarith [(hxo n).2]
    exact le_of_mul_le_mul_left h2 (by linarith)
  have hscaled : Tendsto (fun n ↦ (p : ℤ_[p]) * ((x n).order : ℤ_[p])) atTop
      (𝓝 ((A.order : ℤ_[p]) + b)) := by
    refine (tendsto_const_nhds.add hlimit).congr fun n ↦ ?_
    exact_mod_cast ((hxo n).2).symm
  obtain ⟨m, hm, hxm⟩ := PadicInt.exists_tendsto_of_prime_mul_tendsto hscaled
  rw [padic_limit_order_eq_zero_of_approximate_invariance p hf1 hf (fun n ↦ (hxo n).1) hxm
    happrox, mul_zero] at hm
  rw [← order_coefficientPrimitive_derivative U ha]
  linear_combination -hm

end LaurentSeries
