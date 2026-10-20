/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative

/-!
# The valuation bound at derivative level `e`

Let `k` be a field of characteristic `p`, let `d ≥ 1` with `d ≡ -1 (mod p)`, and let
`g = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ∈ kˣ`. If `h ∈ k((T))` satisfies
`h ∘ g = (g')^(p - 1) h`, `h' ≠ 0` and `v_T(h') ≤ p - 2`, then `v_T(h) ≤ p - 1 - d`.

Let `O` be a discrete valuation ring with residue field `κ = 𝔽_p`, `p ≠ 0` in `O`, and let
`e = v(p)` be its absolute ramification index. Let `P, G ∈ (O ⧸ 𝔪 ^ (r + 1))((T))`, where `P`
reduces to `T ^ p` in `κ((T))`, `G ∘ P = P ∘ G` and the derivative level of `P` is `s(P) = e`,
and let the reduction `f` of `G` satisfy `f = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with
`α ∈ κˣ`, `d ≥ 1` and `d ≡ -1 (mod p)`. Then the normalized derivative satisfies
`v_T(h_P) ≤ p - 1 - d` (Yuan, Theorem 3.1, where `r = e`).

## Main results

* `LaurentSeries.order_le_of_subst_eq_derivative_pow_mul`: the bound `v_T(h) ≤ p - 1 - d` over a
  field of characteristic `p`.
* `FalseTateNonliftability.Truncation.order_normalizedDerivative_le`: Yuan, Theorem 3.1.

## References

* Yuan, Theorem 3.1.
-/

@[expose] public section

noncomputable section

open IsLocalRing (ResidueField)

namespace LaurentSeries

section CommRing

variable {R : Type*} [CommRing R]

private theorem pow_sub_one_mem_orderAddSubgroup {x : LaurentSeries R} {m : ℤ} (hm : 0 ≤ m)
    (hx : x - 1 ∈ orderAddSubgroup m) (n : ℕ) : x ^ n - 1 ∈ orderAddSubgroup m := by
  have hx0 : x ∈ orderAddSubgroup 0 := by
    simpa only [map_one, sub_add_cancel] using add_mem (orderAddSubgroup_antitone hm hx)
      (ofPowerSeries_mem_orderAddSubgroup_zero (1 : PowerSeries R))
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show x ^ n * x - 1 = (x ^ n - 1) * x + (x - 1) by ring]
    exact add_mem (by simpa only [add_zero] using mul_mem_orderAddSubgroup ih hx0) hx

private theorem sub_X_mem_of_normalForm {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d) {α : R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
  mem_orderAddSubgroup_of_sub_single_mem (orderAddSubgroup_antitone (by omega) hg)

private theorem derivative_sub_one_mem_of_normalForm (p : ℕ) [CharP R p] {g : LaurentSeries R}
    {d : ℤ} (hdiv : (p : ℤ) ∣ d + 1) {α : R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    derivative R g - 1 ∈ orderAddSubgroup (2 * d) := by
  have hcast : ((d + 1 : ℤ) : R) = 0 := by
    obtain ⟨n, hn⟩ := hdiv
    rw [hn, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero R p, zero_mul]
  simpa [hcast] using derivative_mem_orderAddSubgroup _ _ hg

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Let `k` have characteristic `p`, let `g = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ≠ 0`,
`d ≥ 1` and `d ≡ -1 (mod p)`, and let `h ∈ k((T))` satisfy `h ∘ g = (g')^(p - 1) h`, `h' ≠ 0` and
`v_T(h') ≤ p - 2`. Then `v_T(h) ≤ p - 1 - d` (Yuan, proof of Theorem 3.1). -/
theorem order_le_of_subst_eq_derivative_pow_mul (p : ℕ) [CharP k p] {g : LaurentSeries k}
    {d : ℤ} (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1) {α : k} (hα : α ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1))
    {h : LaurentSeries k} (hD : derivative k h ≠ 0)
    (hDorder : (derivative k h).order ≤ (p : ℤ) - 2)
    (hchain : subst g h = derivative k g ^ (p - 1) * h) :
    h.order ≤ (p : ℤ) - 1 - d := by
  have hX := sub_X_mem_of_normalForm hd hg
  have hXorder : (g - HahnSeries.single (1 : ℤ) 1).order = d + 1 :=
    order_eq_of_sub_single_mem hα (orderAddSubgroup_antitone (by omega) hg)
  have hXne : g - HahnSeries.single (1 : ℤ) 1 ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.order_zero] at hXorder
    omega
  have hdiff : subst g h - h ∈ orderAddSubgroup (h.order + 2 * d) := by
    rw [hchain, show derivative k g ^ (p - 1) * h - h = (derivative k g ^ (p - 1) - 1) * h by
      ring, add_comm]
    exact mul_mem_orderAddSubgroup (pow_sub_one_mem_orderAddSubgroup (by omega)
      (derivative_sub_one_mem_of_normalForm p hdiv hg) _) (mem_orderAddSubgroup_order h)
  have hprod : (g - HahnSeries.single (1 : ℤ) 1) * derivative k h ∈
      orderAddSubgroup (h.order + 2 * d) := by
    simpa only [sub_sub_cancel] using
      sub_mem hdiff (subst_taylor_mem_orderAddSubgroup hd hX (mem_orderAddSubgroup_order h))
  rw [mem_orderAddSubgroup, ← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hXne hD),
    WithTop.coe_le_coe, HahnSeries.order_mul hXne hD, hXorder] at hprod
  omega

end Field

end LaurentSeries

namespace FalseTateNonliftability.Truncation

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
  (p : ℕ) [Fact p.Prime] [Fact (Nat.card (ResidueField O) = p)] [NeZero (p : O)]

/-- **Theorem 3.1** (Yuan), valuation bound at level `e`. Let `p ≠ 0` in `O`, let `κ = 𝔽_p` and
`e = v(p)`. Let `P, G ∈ (O ⧸ 𝔪 ^ (r + 1))((T))`, where `P` reduces to `T ^ p`,
`G ∘ P = P ∘ G` and `s(P) = e`, and let the reduction `f` of `G` satisfy
`f = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ≠ 0`, `d ≥ 1` and `d ≡ -1 (mod p)`. Then
`v_T(h_P) ≤ p - 1 - d`. -/
theorem order_normalizedDerivative_le {P G : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hcomm : subst P G = subst G P) (hs : derivativeLevel P = absoluteRamificationIdx p O)
    {d : ℤ} (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1) {α : ResidueField O} (hα : α ≠ 0)
    (hG : mapRingHom (residue O r) G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1)) :
    (normalizedDerivative P).order ≤ (p : ℤ) - 1 - d := by
  have := charP_of_natCard_eq_prime (Fact.out : Nat.card (ResidueField O) = p)
  have hX := sub_X_mem_of_normalForm hd hG
  have hadm : IsAdmissible G := (isAdmissible_mapRingHom_iff (residue O r) G).mp
    (isAdmissible_of_sub_X_mem (orderAddSubgroup_antitone (by omega) hX))
  have h1 : (mapRingHom (residue O r) G).coeff 1 ≠ 0 := by
    have hc := (mem_orderAddSubgroup_iff_coeff _ _).mp hX 1 (by omega)
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
    rw [hc]
    exact one_ne_zero
  exact order_le_of_subst_eq_derivative_pow_mul p hd hdiv hα hG
    (derivative_normalizedDerivative_ne_zero p hP hs)
    (order_derivative_normalizedDerivative_le p hP hs)
    (subst_normalizedDerivative_of_commute p hP hadm h1 hcomm)

end FalseTateNonliftability.Truncation
