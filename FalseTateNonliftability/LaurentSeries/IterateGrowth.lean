/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Growth of the ramification numbers of `p`-power iterates

Let `k` be a field of characteristic `p` and let `σ : x ↦ x(f)` be the automorphism of `k((T))`
given by a power series `f = T + O(T ^ 2)`. Then `i(σ ^ p) ≥ p i(σ)`. If `σ` has infinite order,
then `σ ^ n ≠ 1` for every `n > 0`, so the ramification numbers `d_n = i(σ ^ (p ^ n))` are
positive integers; they satisfy `d_(n+1) ≥ p d_n`, hence strictly increase and tend to infinity.

## Main results

* `PowerSeries.mul_ramificationNumber_le_ramificationNumber_iterate`: `p i(σ) ≤ i(σ ^ p)`.
* `PowerSeries.one_le_ramificationNumber_iterate`: `i(σ ^ n) ≥ 1` for `n > 0` if `σ` has infinite
  order.
* `PowerSeries.strictMono_ramificationNumber_iterate_pow`: `n ↦ i(σ ^ (p ^ n))` is strictly
  increasing.
* `PowerSeries.tendsto_ramificationNumber_iterate_pow_atTop`: `i(σ ^ (p ^ n)) → ∞`.

## References

* Yuan, proof of Lemma 4.2.
-/

@[expose] public section

noncomputable section

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

/-- If `f = T + O(T ^ 2)` and `x ↦ x(f)` has infinite order, then `f^{∘n}` has positive
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

/-- If `f = T + O(T ^ 2)` and `x ↦ x(f)` has infinite order, then
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

/-- If `f = T + O(T ^ 2)` and `x ↦ x(f)` has infinite order, then the ramification numbers
`i(σ ^ (p ^ n))` strictly increase. -/
theorem strictMono_ramificationNumber_iterate_pow {f : k⟦X⟧} (hf1 : f.coeff 1 = 1)
    (hf : ¬ IsOfFinOrder (substEquiv f)) :
    StrictMono fun n : ℕ ↦ (iterate f (p ^ n)).ramificationNumber := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h := mul_ramificationNumber_iterate_pow_le p hf1 hf n
  have h1 := one_le_ramificationNumber_iterate hf1 hf (pow_pos (Fact.out : p.Prime).pos n)
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  nlinarith

/-- If `f = T + O(T ^ 2)` and `x ↦ x(f)` has infinite order, then the ramification numbers
`i(σ ^ (p ^ n))` tend to infinity. -/
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
