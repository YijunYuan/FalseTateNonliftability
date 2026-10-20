/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.PrimitiveNormalization
public import FalseTateNonliftability.LaurentSeries.FrobeniusKernel
public import FalseTateNonliftability.LaurentSeries.IterateGrowth
public import FalseTateNonliftability.LaurentSeries.ApproximateInvariants
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The p-adic ramification limit of an exact invariant differential

An invariant nonzero exact differential for an actual infinite-order
substitution over the prime field determines the p-adic limit of the
ramification numbers. The proof uses actual finite orbit sums of a
Frobenius root and the original Laurent coefficients, allowing negative
primitive orders. This is Yuan, Proposition 4.2 (`nl:exact-differential-limit`).
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped Topology

namespace PadicInt

/-- Division by the prime is continuous on its actual closed image: a
convergent sequence of prime multiples has a convergent sequence of factors. -/
theorem exists_tendsto_of_prime_mul_tendsto {p : ℕ} [Fact p.Prime]
    (x : ℕ → PadicInt p) (b : PadicInt p)
    (h : Tendsto (fun n ↦ (p : PadicInt p) * x n) atTop (nhds b)) :
    ∃ c : PadicInt p, (p : PadicInt p) * c = b ∧ Tendsto x atTop (nhds c) := by
  have hp : (p : PadicInt p) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have he : IsClosedEmbedding (fun z : PadicInt p ↦ (p : PadicInt p) * z) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (fun _ _ h ↦ mul_left_cancel₀ hp h)
  have hb : b ∈ Set.range (fun z : PadicInt p ↦ (p : PadicInt p) * z) :=
    he.isClosed_range.mem_of_tendsto h (Eventually.of_forall fun n ↦ ⟨x n, rfl⟩)
  obtain ⟨c, hc⟩ := hb
  change (p : PadicInt p) * c = b at hc
  refine ⟨c, hc, he.tendsto_nhds_iff.mpr ?_⟩
  change Tendsto (fun n ↦ (p : PadicInt p) * x n) atTop (nhds ((p : PadicInt p) * c))
  rw [hc]
  exact h

end PadicInt

namespace LaurentSeries

section OrbitSum

variable {k : Type*} [Field k]

/-- The original finite orbit sum of an actual coboundary telescopes. -/
theorem sum_pow_apply_sub (E : LaurentSeries k ≃ₐ[k] LaurentSeries k)
    (A : LaurentSeries k) (N : ℕ) :
    ∑ j ∈ Finset.range N, (E ^ j) (E A - A) = (E ^ N) A - A := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
    abel

/-- Taking the characteristic-prime power of the actual orbit sum of a
Frobenius root gives the actual iterated displacement. -/
theorem orbit_sum_pow_eq_iterate_sub (p : ℕ) [Fact p.Prime] [CharP k p]
    (E : LaurentSeries k ≃ₐ[k] LaurentSeries k) (A B : LaurentSeries k)
    (hB : B ^ p = E A - A) (N : ℕ) :
    (∑ j ∈ Finset.range N, (E ^ j) B) ^ p = (E ^ N) A - A := by
  have : CharP (LaurentSeries k) p :=
    ((algebraMap k (LaurentSeries k)).charP_iff_charP p).mp inferInstance
  rw [sum_pow_char]
  simp only [← map_pow, hB, sum_pow_apply_sub]

/-- The actual defect of a finite orbit sum is the endpoint displacement. -/
theorem subst_orbit_sum_sub (E : LaurentSeries k ≃ₐ[k] LaurentSeries k)
    (B : LaurentSeries k) (N : ℕ) :
    E (∑ j ∈ Finset.range N, (E ^ j) B) - ∑ j ∈ Finset.range N, (E ^ j) B =
      (E ^ N) B - B := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, map_add]
    calc
      _ = (E (∑ j ∈ Finset.range N, (E ^ j) B) - ∑ j ∈ Finset.range N, (E ^ j) B) +
          (E ((E ^ N) B) - (E ^ N) B) := by abel
      _ = (E ^ N) B - B + ((E ^ (N + 1)) B - (E ^ N) B) := by
        rw [ih, ← AlgEquiv.mul_apply, ← pow_succ']
      _ = _ := by abel

end OrbitSum

section Displacement

variable {k : Type*} [Field k]

local instance exactDifferentialZeroSpanIsMaximal :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- A nondivisible input order gives an actual nonzero displacement with the
exact expected order, even when that order is zero or negative. -/
theorem subst_sub_ne_zero_and_order_eq_of_not_dvd (p : ℕ) [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (d : ℤ) (hd : 1 ≤ d)
    (hg : (g - HahnSeries.single (1 : ℤ) 1).orderTop = ((d + 1 : ℤ) : WithTop ℤ))
    (x : LaurentSeries k) (hx : x ≠ 0) (hm : ¬ (p : ℤ) ∣ x.order) :
    subst 0 IsNilpotent.zero g hG x - x ≠ 0 ∧
      (subst 0 IsNilpotent.zero g hG x - x).order = x.order + d := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  have hδ : δ ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hg]; exact WithTop.coe_ne_top)
  have hδorder : δ.order = d + 1 := by
    have h := (HahnSeries.order_eq_orderTop_of_ne_zero hδ).trans hg
    exact WithTop.coe_injective h
  let α := δ.coeff δ.order
  have hα : α ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hδ
  have htail : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2) := by
    have h := sub_leadingTerm_mem_orderAddSubgroup δ
    change δ - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + 2)
    simpa only [α, hδorder, show d + 1 + 1 = d + 2 by omega] using h
  have hlead := subst_sub_leadingTerm_mem g hG d hd α htail x x.order (x.coeff x.order)
    (sub_leadingTerm_mem_orderAddSubgroup x)
  have hβ : (x.order : k) * α * x.coeff x.order ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mt (CharP.intCast_eq_zero_iff k p x.order).mp hm) hα)
      (HahnSeries.coeff_order_eq_zero.not.mpr hx)
  have hc := (mem_orderAddSubgroup_iff_coeff (x.order + d + 1) _).mp hlead
    (x.order + d) (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  refine ⟨HahnSeries.ne_zero_of_coeff_ne_zero (hc ▸ hβ), ?_⟩
  exact order_subst_sub_eq_of_not_dvd p g hG d hd α hα htail x hx hm

/-- The actual prime-power orbit sums are nonzero and have the exact signed
integer order dictated by the normalized primitive. Nonvanishing is established
before the ordinary order calculation. -/
theorem primePower_orbit_sum_ne_zero_and_order (p : ℕ) [Fact p.Prime]
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (A : LaurentSeries (ZMod p)) (hA : A ≠ 0) (hq : ¬ (p : ℤ) ∣ A.order)
    (B : LaurentSeries (ZMod p))
    (hB : B ^ p = powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one) A - A) :
    let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)
    ∀ n : ℕ, let x := ∑ j ∈ Finset.range (p ^ n), (E ^ j) B
      x ≠ 0 ∧ (p : ℤ) * x.order = A.order +
        ((HahnSeries.ofPowerSeries ℤ (ZMod p) (powerSeriesIterate f (p ^ n)) -
          HahnSeries.single (1 : ℤ) 1).order - 1) := by
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
    (by rw [hlinear]; exact isUnit_one)
  dsimp only
  intro n
  let g := powerSeriesIterate f (p ^ n)
  let δ := HahnSeries.ofPowerSeries ℤ (ZMod p) g - HahnSeries.single (1 : ℤ) 1
  let d := δ.order - 1
  have hg0 : g.constantCoeff = 0 := (powerSeriesIterate_spec f hf _).1
  have hg1 : g.coeff 1 = 1 := by
    rw [(powerSeriesIterate_spec f hf _).2, hlinear, one_pow]
  have hδ : δ ≠ 0 := powerSeriesIterate_displacement_ne_zero f hf _ hinfinite _
    (pow_pos (Fact.out : p.Prime).pos n)
  have hd : 1 ≤ d := by
    have h := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite _
      (pow_pos (Fact.out : p.Prime).pos n)
    change 2 ≤ δ.order at h
    dsimp only [d]
    omega
  have hδtop : δ.orderTop = ((d + 1 : ℤ) : WithTop ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hδ]
    congr 1
    dsimp only [d]
    omega
  have hiter : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0
      (by rw [hg1]; exact isUnit_one) = E ^ (p ^ n) :=
    powerSeriesSubstEquiv_powerSeriesIterate f hf _ (p ^ n)
  have ho := subst_sub_ne_zero_and_order_eq_of_not_dvd p
    (HahnSeries.ofPowerSeries ℤ (ZMod p) g)
    (isAdmissible_ofPowerSeries 0 g hg0 (by rw [hg1]; exact isUnit_one))
    d hd hδtop A hA hq
  have hpow : (∑ j ∈ Finset.range (p ^ n), (E ^ j) B) ^ p =
      subst 0 IsNilpotent.zero (HahnSeries.ofPowerSeries ℤ (ZMod p) g)
        (isAdmissible_ofPowerSeries 0 g hg0 (by rw [hg1]; exact isUnit_one)) A - A := by
    rw [orbit_sum_pow_eq_iterate_sub p E A B hB, ← hiter]
    rfl
  refine ⟨?_, ?_⟩
  · intro hx
    apply ho.1
    rw [← hpow, hx, zero_pow (Fact.out : p.Prime).ne_zero]
  · have h := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_pow, ho.2, nsmul_eq_mul] at h
    exact h

/-- The genuine orbit sums satisfy every relative precision bound. Signed
primitive orders and zero defects are both retained in the subgroup formulation. -/
theorem primePower_orbit_sum_approximate_invariance (p : ℕ) [Fact p.Prime]
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (A : LaurentSeries (ZMod p)) (hA : A ≠ 0) (hq : ¬ (p : ℤ) ∣ A.order)
    (B : LaurentSeries (ZMod p))
    (hB : B ^ p = powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one) A - A) :
    let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)
    let x := fun n : ℕ ↦ ∑ j ∈ Finset.range (p ^ n), (E ^ j) B
    ∀ N : ℤ, ∀ᶠ n in atTop, E (x n) - x n ∈ orderAddSubgroup ((x n).order + N) := by
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
    (by rw [hlinear]; exact isUnit_one)
  let x := fun n : ℕ ↦ ∑ j ∈ Finset.range (p ^ n), (E ^ j) B
  let d := fun n : ℕ ↦ (HahnSeries.ofPowerSeries ℤ (ZMod p)
    (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1
  have ht : Tendsto d atTop atTop :=
    tendsto_primePowerIterate_ramification_atTop p f hf hlinear hinfinite
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  dsimp only
  intro N
  filter_upwards [Filter.tendsto_atTop.1 ht (max 0 (A.order + (p : ℤ) * (N - B.order)))] with n hn
  have hd0 : 0 ≤ d n := (le_max_left _ _).trans hn
  have hlarge : A.order + (p : ℤ) * (N - B.order) ≤ d n := (le_max_right _ _).trans hn
  have horder := (primePower_orbit_sum_ne_zero_and_order p f hf hlinear hinfinite A hA hq B hB n).2
  change (p : ℤ) * (x n).order = A.order + d n at horder
  have hbound : (x n).order + N ≤ B.order + d n := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hp) hd0
    nlinarith
  let g := powerSeriesIterate f (p ^ n)
  have hg0 : g.constantCoeff = 0 := (powerSeriesIterate_spec f hf _).1
  have hg1 : g.coeff 1 = 1 := by
    rw [(powerSeriesIterate_spec f hf _).2, hlinear, one_pow]
  have hd : 1 ≤ d n := by
    have h := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite _
      (pow_pos (Fact.out : p.Prime).pos n)
    dsimp only [d]
    omega
  have hmem : HahnSeries.ofPowerSeries ℤ (ZMod p) g - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup (d n + 1) := by
    dsimp only [d]
    rw [sub_add_cancel]
    exact mem_orderAddSubgroup_order _
  have hb := subst_sub_mem_orderAddSubgroup (HahnSeries.ofPowerSeries ℤ (ZMod p) g)
    (isAdmissible_ofPowerSeries 0 g hg0 (by rw [hg1]; exact isUnit_one))
    (d n) hd hmem B.order B (mem_orderAddSubgroup_order B)
  have hiter : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0
      (by rw [hg1]; exact isUnit_one) = E ^ (p ^ n) :=
    powerSeriesSubstEquiv_powerSeriesIterate f hf _ (p ^ n)
  have hdef : E (x n) - x n =
      subst 0 IsNilpotent.zero (HahnSeries.ofPowerSeries ℤ (ZMod p) g)
        (isAdmissible_ofPowerSeries 0 g hg0 (by rw [hg1]; exact isUnit_one)) B - B := by
    rw [subst_orbit_sum_sub, ← hiter]
    rfl
  change E (x n) - x n ∈ orderAddSubgroup ((x n).order + N)
  rw [hdef]
  exact orderAddSubgroup_antitone hbound hb

/-- **An exact invariant differential determines the ramification limit**
(Yuan, Proposition 4.2). A differential is represented by its actual Laurent
coefficient `a`, and invariance is the actual substitution chain-law formula.
No choice of primitive, trace identity or limiting quotient is assumed. -/
theorem padic_ramification_limit_eq_of_invariant_exact_differential
    (p : ℕ) [Fact p.Prime] (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (b : PadicInt p)
    (hlimit : Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ (ZMod p) (powerSeriesIterate f (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop (nhds b))
    (a : LaurentSeries (ZMod p)) (ha : a ≠ 0)
    (hexact : ∃ U : LaurentSeries (ZMod p), derivative (ZMod p) U = a)
    (hinvariant : powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
        (by rw [hlinear]; exact isUnit_one) a *
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) = a) :
    b = -((a.order + 1 : ℤ) : PadicInt p) := by
  obtain ⟨U, hU⟩ := hexact
  have hD : derivative (ZMod p) U ≠ 0 := by rw [hU]; exact ha
  let A := coefficientPrimitive a
  have hAderiv : derivative (ZMod p) A = a := by
    dsimp only [A]
    rw [← hU, derivative_coefficientPrimitive_derivative]
  have hA : A ≠ 0 := by
    intro hzero
    apply ha
    rw [← hAderiv, hzero, map_zero]
  have hq : ¬ (p : ℤ) ∣ A.order := by
    dsimp only [A]
    rw [← hU]
    exact not_dvd_order_coefficientPrimitive_derivative p U hD
  have hqorder : A.order = a.order + 1 := by
    dsimp only [A]
    rw [← hU]
    exact order_coefficientPrimitive_derivative U hD
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
    (by rw [hlinear]; exact isUnit_one)
  have hzero : derivative (ZMod p) (E A - A) = 0 := by
    rw [map_sub, powerSeriesSubstEquiv_apply, derivative_subst, hAderiv]
    change E a * derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) - a = 0
    exact sub_eq_zero.mpr hinvariant
  obtain ⟨B, hB⟩ := (derivative_eq_zero_iff_exists_pow p (E A - A)).mp hzero
  let x := fun n : ℕ ↦ ∑ j ∈ Finset.range (p ^ n), (E ^ j) B
  let d := fun n : ℕ ↦ (HahnSeries.ofPowerSeries ℤ (ZMod p)
    (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1
  have hx : ∀ n, x n ≠ 0 := fun n ↦
    (primePower_orbit_sum_ne_zero_and_order p f hf hlinear hinfinite A hA hq B hB n).1
  have ho (n : ℕ) : (p : ℤ) * (x n).order = A.order + d n :=
    (primePower_orbit_sum_ne_zero_and_order p f hf hlinear hinfinite A hA hq B hB n).2
  have hscaled : Tendsto (fun n : ℕ ↦ (p : PadicInt p) * ((x n).order : PadicInt p))
      atTop (nhds ((A.order : PadicInt p) + b)) := by
    have hfun : (fun n : ℕ ↦ (p : PadicInt p) * ((x n).order : PadicInt p)) =
        (fun n : ℕ ↦ (A.order : PadicInt p) + ((d n : ℤ) : PadicInt p)) := by
      funext n
      exact_mod_cast ho n
    rw [hfun]
    exact tendsto_const_nhds.add hlimit
  obtain ⟨m, hm, hxm⟩ := PadicInt.exists_tendsto_of_prime_mul_tendsto
    (fun n ↦ ((x n).order : PadicInt p)) ((A.order : PadicInt p) + b) hscaled
  have hmzero := padic_limit_order_eq_zero_of_approximate_invariance f hf hlinear hinfinite
    x hx m hxm (primePower_orbit_sum_approximate_invariance p f hf hlinear hinfinite A hA hq B hB)
  rw [hmzero, mul_zero] at hm
  rw [← hqorder]
  linear_combination -hm

end Displacement

end LaurentSeries
