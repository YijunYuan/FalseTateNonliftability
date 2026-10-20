/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative
public import Mathlib.Algebra.CharP.LinearMaps

/-!
# Laurent coordinates and normal forms

Actual power-series coordinates act through the canonical Laurent substitution
automorphisms. Coordinate invariance, the resonant coefficient computation,
and successive nonresonant coefficient removal yield the normal form controlled
by the next ramification number. Order bounds include the identity case through
the canonical `orderTop` and retain all integer Laurent exponents.

This proves blueprint nodes `nl:ramification-coordinate-invariance`,
`nl:resonant-coefficient`, `nl:remove-coefficient`, and `nl:normal-form`.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

variable {k : Type*} [Field k]

local instance normalFormZeroSpanIsMaximal : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The linear coefficient of an actual zero-constant power-series
substitution, obtained from the canonical chain rule. -/
theorem coeff_one_powerSeries_subst (f w : PowerSeries k) (hf : f.constantCoeff = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst f w) = w.coeff 1 * f.coeff 1 := by
  have h := congrArg PowerSeries.constantCoeff
    (PowerSeries.derivative_subst (f := w) (g := f)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf))
  have hc : PowerSeries.constantCoeff (PowerSeries.subst f (PowerSeries.derivative w)) =
      PowerSeries.constantCoeff (PowerSeries.derivative w) := by
    simpa only [PowerSeries.constantCoeff_eq, Algebra.algebraMap_self_apply] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf (PowerSeries.derivative w)
  rw [map_mul, hc] at h
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
    zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using h

/-- Actual power-series coordinate substitution preserves `orderTop`,
including the zero series. The finite-order computation is reused. -/
theorem orderTop_powerSeriesSubstEquiv (w : PowerSeries k) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) (f : LaurentSeries k) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear f).orderTop = f.orderTop := by
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  by_cases hf : f = 0
  · simp only [hf, map_zero]
  have hEf : E f ≠ 0 := fun h ↦ hf (E.injective (by simpa only [map_zero] using h))
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hEf,
    FalseTateNonliftability.CoefficientRing.order_powerSeriesSubstEquiv w hw hwlinear,
    HahnSeries.order_eq_orderTop_of_ne_zero hf]

/-- The actual inverse coordinate preserves the same order bound. -/
theorem orderTop_powerSeriesSubstEquiv_symm (w : PowerSeries k) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) (f : LaurentSeries k) :
    ((powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm f).orderTop = f.orderTop := by
  have h := orderTop_powerSeriesSubstEquiv w hw hwlinear
    ((powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm f)
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

/-- Conjugation is ordinary composition of the original power series with
Mathlib's actual inverse coordinate. -/
def powerSeriesConjugate (f w : PowerSeries k) (hwlinear : IsUnit (w.coeff 1)) : PowerSeries k :=
  PowerSeries.subst (w.substInvOfIsUnit hwlinear) (PowerSeries.subst f w)

/-- The same conjugation is the canonical Laurent coordinate automorphism
applied to the actual substituted coordinate. -/
theorem ofPowerSeries_powerSeriesConjugate (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm
        (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
          (HahnSeries.ofPowerSeries ℤ k w)) := by
  have hQlinear : IsUnit ((w.substInvOfIsUnit hwlinear).coeff 1) := by
    rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact Units.isUnit _
  rw [powerSeriesSubstEquiv_apply,
    subst_ofPowerSeries 0 IsNilpotent.zero f hf hflinear w,
    powerSeriesSubstEquiv_symm_apply,
    subst_ofPowerSeries 0 IsNilpotent.zero _
      (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) hQlinear]
  rfl

/-- The actual conjugate remains zero-constant. -/
theorem constantCoeff_powerSeriesConjugate (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    (powerSeriesConjugate f w hwlinear).constantCoeff = 0 := by
  have hc : PowerSeries.constantCoeff (PowerSeries.subst f w) = 0 := by
    simpa only [PowerSeries.constantCoeff_eq] using
      PowerSeries.constantCoeff_subst_eq_zero hf w hw
  simpa only [powerSeriesConjugate, PowerSeries.constantCoeff_eq] using
    PowerSeries.constantCoeff_subst_eq_zero
      (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) (PowerSeries.subst f w) hc

/-- Coordinate conjugation preserves the actual linear coefficient. -/
theorem coeff_one_powerSeriesConjugate (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    (powerSeriesConjugate f w hwlinear).coeff 1 = f.coeff 1 := by
  have hi := congrArg (PowerSeries.coeff 1)
    (PowerSeries.subst_substInvOfIsUnit_right w hw hwlinear)
  rw [coeff_one_powerSeries_subst _ w
    (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear)] at hi
  have hmul : w.coeff 1 * (w.substInvOfIsUnit hwlinear).coeff 1 = 1 := by simpa using hi
  change PowerSeries.coeff 1
    (PowerSeries.subst (w.substInvOfIsUnit hwlinear) (PowerSeries.subst f w)) = _
  rw [coeff_one_powerSeries_subst _ _ (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear),
    coeff_one_powerSeries_subst f w hf]
  calc
    _ = f.coeff 1 * (w.coeff 1 * (w.substInvOfIsUnit hwlinear).coeff 1) := by ring
    _ = f.coeff 1 := by rw [hmul, mul_one]

/-- Zero-constant embedded power series have support in positive degrees. -/
theorem ofPowerSeries_mem_orderAddSubgroup_one (f : PowerSeries k)
    (hf : f.constantCoeff = 0) : HahnSeries.ofPowerSeries ℤ k f ∈ orderAddSubgroup 1 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  by_cases hj0 : j < 0
  · rw [PowerSeries.coeff_coe, ite_eq_left hj0]
  · have hjz : j = 0 := by omega
    subst j
    simpa only [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf

/-- The linear term removes the only possible degree-one coefficient. -/
theorem ofPowerSeries_sub_linear_mem_two (f : PowerSeries k) (hf : f.constantCoeff = 0) :
    HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) (f.coeff 1) ∈
      orderAddSubgroup 2 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sub]
  by_cases hj1 : j = 1
  · subst j
    simp only [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_single_same, sub_self]
  · rw [(mem_orderAddSubgroup_iff_coeff 1 _).mp
      (ofPowerSeries_mem_orderAddSubgroup_one f hf) j (by omega),
      HahnSeries.coeff_single_of_ne hj1, sub_self]

/-- The conjugated displacement is the inverse coordinate applied to the
actual displacement of the coordinate itself. -/
theorem powerSeriesConjugate_sub_variable (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) - HahnSeries.single (1 : ℤ) 1 =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm
        (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
          (HahnSeries.ofPowerSeries ℤ k w) - HahnSeries.ofPowerSeries ℤ k w) := by
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  have hx : E (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k w :=
    subst_X 0 IsNilpotent.zero _ _
  have hi : E.symm (HahnSeries.ofPowerSeries ℤ k w) = HahnSeries.single (1 : ℤ) 1 := by
    rw [← hx, AlgEquiv.symm_apply_apply]
  rw [ofPowerSeries_powerSeriesConjugate f w hf hflinear hw hwlinear, map_sub]
  change _ = _ - E.symm (HahnSeries.ofPowerSeries ℤ k w)
  rw [hi]

/-- A coordinate and its image under an actual power-series automorphism
have displacement of exactly the same order, including zero displacement. -/
theorem orderTop_powerSeries_displacement (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
      (HahnSeries.ofPowerSeries ℤ k w) - HahnSeries.ofPowerSeries ℤ k w).orderTop =
      (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).orderTop := by
  let δ := HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1
  let B := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
    (HahnSeries.ofPowerSeries ℤ k w) - HahnSeries.ofPowerSeries ℤ k w
  have hB : B = HahnSeries.ofPowerSeries ℤ k (PowerSeries.subst f w) -
      HahnSeries.ofPowerSeries ℤ k w := by
    dsimp only [B]
    rw [powerSeriesSubstEquiv_apply, subst_ofPowerSeries 0 IsNilpotent.zero f hf hflinear w]
  by_cases hδ : δ = 0
  · have hfX : f = PowerSeries.X := by
      have heq : HahnSeries.ofPowerSeries ℤ k f = HahnSeries.ofPowerSeries ℤ k PowerSeries.X := by
        simpa only [δ, sub_eq_zero, HahnSeries.ofPowerSeries_X] using hδ
      ext n
      simpa only [HahnSeries.ofPowerSeries_apply_coeff] using
        congrArg (fun x : LaurentSeries k ↦ x.coeff (n : ℤ)) heq
    change B.orderTop = δ.orderTop
    rw [hδ, hB, hfX]
    simp
  by_cases hlinear : f.coeff 1 = 1
  · have hδmem : δ ∈ orderAddSubgroup 2 := by
      simpa only [δ, hlinear] using ofPowerSeries_sub_linear_mem_two f hf
    have hm : 2 ≤ δ.order := by
      change ((2 : ℤ) : WithTop ℤ) ≤ δ.orderTop at hδmem
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hδ] at hδmem
      exact WithTop.coe_le_coe.mp hδmem
    have hδtop : δ.orderTop = ((δ.order - 1 + 1 : ℤ) : WithTop ℤ) := by
      rw [sub_add_cancel, HahnSeries.order_eq_orderTop_of_ne_zero hδ]
    have hD : derivative k (HahnSeries.ofPowerSeries ℤ k w) ≠ 0 :=
      (isUnit_derivative_ofPowerSeries w hwlinear).ne_zero
    have hDorder : (derivative k (HahnSeries.ofPowerSeries ℤ k w)).order = 0 :=
      FalseTateNonliftability.CoefficientRing.order_derivative_ofPowerSeries w hwlinear
    have hb : B.order = δ.order := by
      have ho := order_subst_ofPowerSeries_sub_eq (HahnSeries.ofPowerSeries ℤ k f)
        (isAdmissible_ofPowerSeries 0 f hf hflinear) (δ.order - 1) (by omega) hδtop w
        (by simpa only [← derivative_ofPowerSeries] using hD)
        (by simpa only [← derivative_ofPowerSeries, hDorder] using
          (show (0 : ℤ) < δ.order - 1 + 1 by omega))
      simpa only [B, powerSeriesSubstEquiv_apply, sub_add_cancel,
        ← derivative_ofPowerSeries, hDorder, add_zero] using ho
    have hBne : B ≠ 0 := by
      intro hz
      rw [hz, HahnSeries.order_zero] at hb
      omega
    change B.orderTop = δ.orderTop
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hBne, hb,
      HahnSeries.order_eq_orderTop_of_ne_zero hδ]
  · have hδcoeff : δ.coeff 1 ≠ 0 := by
      dsimp only [δ]
      simpa only [HahnSeries.coeff_sub, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.coeff_single_same, sub_ne_zero] using hlinear
    have hBcoeff : B.coeff 1 ≠ 0 := by
      rw [hB, HahnSeries.coeff_sub, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, coeff_one_powerSeries_subst f w hf]
      rw [show w.coeff 1 * f.coeff 1 - w.coeff 1 = w.coeff 1 * (f.coeff 1 - 1) by ring]
      exact mul_ne_zero hwlinear.ne_zero (sub_ne_zero.mpr hlinear)
    have hδmem : δ ∈ orderAddSubgroup 1 := (orderAddSubgroup 1).sub_mem
      (ofPowerSeries_mem_orderAddSubgroup_one f hf) HahnSeries.orderTop_single_le
    have hBmem : B ∈ orderAddSubgroup 1 := by
      rw [hB]
      exact (orderAddSubgroup 1).sub_mem
        (ofPowerSeries_mem_orderAddSubgroup_one _ (by
          simpa only [PowerSeries.constantCoeff_eq] using
            PowerSeries.constantCoeff_subst_eq_zero hf w hw))
        (ofPowerSeries_mem_orderAddSubgroup_one w hw)
    change B.orderTop = δ.orderTop
    exact (le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hBcoeff) hBmem).trans
      (le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hδcoeff) hδmem).symm

/-- Ramification is independent of an actual invertible power-series
coordinate. Equality is in `WithTop ℤ`, so the identity case is included. -/
theorem orderTop_powerSeriesConjugate_sub_variable (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    (HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) -
      HahnSeries.single (1 : ℤ) 1).orderTop =
    (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).orderTop := by
  rw [powerSeriesConjugate_sub_variable f w hf hflinear hw hwlinear,
    orderTop_powerSeriesSubstEquiv_symm]
  exact orderTop_powerSeries_displacement f w hf hflinear hw hwlinear

/-- Powers preserve actual support lower bounds on the original carrier. -/
theorem pow_mem_orderAddSubgroup (x : LaurentSeries k) (m : ℤ)
    (hx : x ∈ orderAddSubgroup m) (n : ℕ) : x ^ n ∈ orderAddSubgroup ((n : ℤ) * m) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Nat.cast_zero, zero_mul, map_one] using
      ofPowerSeries_mem_orderAddSubgroup_zero (1 : PowerSeries k)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ]
    exact mul_mem_orderAddSubgroup ih hx

/-- The actual substitution-minus-identity operator in the canonical ring
of linear endomorphisms. -/
def substitutionDifference (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) :
    Module.End k (LaurentSeries k) where
  toFun x := subst 0 IsNilpotent.zero g hG x - x
  map_add' x y := by rw [map_add]; abel
  map_smul' a x := by
    change subst 0 IsNilpotent.zero g hG (a • x) - a • x =
      a • (subst 0 IsNilpotent.zero g hG x - x)
    simp only [← HahnSeries.C_mul_eq_smul]
    rw [map_mul]
    have hC : subst 0 IsNilpotent.zero g hG (HahnSeries.C a) = HahnSeries.C a := by
      simpa only [LaurentSeries.algebraMap_apply] using
        (subst 0 IsNilpotent.zero g hG).commutes a
    rw [hC]
    ring

@[simp]
theorem substitutionDifference_apply (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (x : LaurentSeries k) :
    substitutionDifference g hG x = subst 0 IsNilpotent.zero g hG x - x := rfl

/-- The characteristic-prime operator identity uses actual substitution
iteration and the actual difference operator, with no iterate certificate. -/
theorem substitutionDifference_pow_char (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (x : LaurentSeries k) :
    (substitutionDifference g hG ^ p) x = (subst 0 IsNilpotent.zero g hG)^[p] x - x := by
  let S : Module.End k (LaurentSeries k) := substitutionDifference g hG + 1
  let : CharP (Module.End k (LaurentSeries k)) p :=
    ((algebraMap k (Module.End k (LaurentSeries k))).charP_iff_charP p).mp inferInstance
  have hN : substitutionDifference g hG = S - 1 := by dsimp only [S]; abel
  have hp : substitutionDifference g hG ^ p = S ^ p - 1 := by
    rw [hN]
    simpa only [one_pow] using sub_pow_char_of_commute (p := p) (Commute.one_right S)
  have hS : (S : LaurentSeries k → LaurentSeries k) = subst 0 IsNilpotent.zero g hG := by
    funext y
    simp only [S, LinearMap.add_apply, substitutionDifference_apply, Module.End.one_apply,
      sub_add_cancel]
  have h := congrArg (fun F : Module.End k (LaurentSeries k) ↦ F x) hp
  simpa only [LinearMap.sub_apply, Module.End.pow_apply, Module.End.one_apply, hS] using h

/-- Iterating the actual difference operator raises every integer support
lower bound by `n*d`, including negative starting bounds and zero inputs. -/
theorem substitutionDifference_pow_mem (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (n : ℕ) (m : ℤ) (x : LaurentSeries k) (hx : x ∈ orderAddSubgroup m) :
    (substitutionDifference g hG ^ n) x ∈ orderAddSubgroup (m + (n : ℤ) * d) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, add_zero] using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, substitutionDifference_apply]
    have heq : m + ((n + 1 : ℕ) : ℤ) * d = (m + (n : ℤ) * d) + d := by
      push_cast
      ring
    rw [heq]
    exact subst_sub_mem_orderAddSubgroup g hG d hd hg _ _ ih

/-- The finite iterated leading coefficient is computed on the actual
Laurent difference operator; all integer monomial degrees are retained. -/
theorem substitutionDifference_pow_leadingTerm_mem (g : LaurentSeries k)
    (hG : IsAdmissible (0 : k) g) (d : ℤ) (hd : 1 ≤ d) (α : k)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2))
    (x : LaurentSeries k) (m : ℤ) (b : k)
    (hx : x - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) (n : ℕ) :
    (substitutionDifference g hG ^ n) x - HahnSeries.single (m + (n : ℤ) * d)
      (b * ∏ i ∈ Finset.range n, (((m + (i : ℤ) * d : ℤ) : k) * α)) ∈
        orderAddSubgroup (m + (n : ℤ) * d + 1) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, add_zero,
      Finset.range_zero, Finset.prod_empty, mul_one] using hx
  | succ n ih =>
    have hm : m + ((n + 1 : ℕ) : ℤ) * d = (m + (n : ℤ) * d) + d := by
      push_cast
      ring
    have hb : b * ∏ i ∈ Finset.range (n + 1), (((m + (i : ℤ) * d : ℤ) : k) * α) =
        (((m + (n : ℤ) * d : ℤ) : k) * α) *
          (b * ∏ i ∈ Finset.range n, (((m + (i : ℤ) * d : ℤ) : k) * α)) := by
      rw [Finset.prod_range_succ]
      ring
    rw [pow_succ', Module.End.mul_apply, substitutionDifference_apply, hm, hb]
    exact subst_sub_leadingTerm_mem g hG d hd α hg _ _ _ ih

/-- Actual substitution commutes with Frobenius before taking the difference. -/
theorem substitutionDifference_frobenius (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (x : LaurentSeries k) :
    substitutionDifference g hG (x ^ p) = (substitutionDifference g hG x) ^ p := by
  let : CharP (LaurentSeries k) p := ((algebraMap k (LaurentSeries k)).charP_iff_charP p).mp inferInstance
  simp only [substitutionDifference_apply, map_pow]
  exact (sub_pow_char (p := p) (x := subst 0 IsNilpotent.zero g hG x) (y := x)).symm

/-- A monomial whose degree is divisible by `p` contributes only above the
resonant degree. This is a support estimate on the actual Frobenius image. -/
theorem substitutionDifference_divisible_monomial_mem (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (d : ℤ) (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (hdiv : (p : ℤ) ∣ d + 1) (α : k) :
    substitutionDifference g hG (HahnSeries.single (d + 1) α) ∈
      orderAddSubgroup (((p : ℤ) + 1) * d + 1) := by
  obtain ⟨q, hq⟩ := hdiv
  have hmon : (HahnSeries.single q (1 : k)) ^ p = HahnSeries.single (d + 1) 1 := by
    simp only [HahnSeries.single_pow, one_pow, nsmul_eq_mul, ← hq]
  have hb := subst_sub_mem_orderAddSubgroup g hG d hd hg q (HahnSeries.single q 1)
    HahnSeries.orderTop_single_le
  change substitutionDifference g hG (HahnSeries.single q 1) ∈ orderAddSubgroup (q + d) at hb
  have hp := pow_mem_orderAddSubgroup _ (q + d) hb p
  rw [← substitutionDifference_frobenius p g hG, hmon] at hp
  have heq : (p : ℤ) * (q + d) = ((p : ℤ) + 1) * d + 1 := by nlinarith [hq]
  rw [heq] at hp
  have hsingle : (HahnSeries.single (d + 1) α : LaurentSeries k) =
      α • HahnSeries.single (d + 1) 1 := by
    rw [← HahnSeries.C_mul_eq_smul]
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hsingle, LinearMap.map_smul]
  exact hp.trans (HahnSeries.orderTop_le_orderTop_smul α _)

/-- Every factor of the actual resonant leading coefficient is nonzero;
the last index is `p-2`, so this also includes the characteristic-two case. -/
theorem resonantLeadingProduct_ne_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    (d ℓ : ℤ) (hd : (p : ℤ) ∣ d + 1) (hℓ : (p : ℤ) ∣ ℓ + 1)
    (α : k) (hα : α ≠ 0) :
    (∏ i ∈ Finset.range (p - 1), (((ℓ + (i : ℤ) * d : ℤ) : k) * α)) ≠ 0 := by
  have hcast (m : ℤ) (hm : (p : ℤ) ∣ m + 1) : (m : k) = -1 := by
    obtain ⟨q, hq⟩ := hm
    have hz : ((m + 1 : ℤ) : k) = 0 := by
      rw [hq, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero k p, zero_mul]
    exact eq_neg_of_add_eq_zero_left (by simpa only [Int.cast_add, Int.cast_one] using hz)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply mul_ne_zero _ hα
  have heq : ((ℓ + (i : ℤ) * d : ℤ) : k) = -((i + 1 : ℕ) : k) := by
    push_cast
    rw [hcast ℓ hℓ, hcast d hd]
    ring
  rw [heq, neg_ne_zero]
  exact (CharP.cast_eq_zero_iff k p (i + 1)).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hi; omega))

/-- A nonzero resonant coefficient gives the exact next displacement
order. This is the actual prime-fold substitution iterate, not an assumed
ramification formula. -/
theorem resonant_iterate_orderTop (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d ℓ : ℤ) (hd : 1 ≤ d) (hlo : d + 2 ≤ ℓ) (hhi : ℓ ≤ 2 * d)
    (hdp : (p : ℤ) ∣ d + 1) (hℓp : (p : ℤ) ∣ ℓ + 1)
    (α β : k) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α -
      HahnSeries.single ℓ β ∈ orderAddSubgroup (ℓ + 1)) :
    ((subst 0 IsNilpotent.zero g hG)^[p] (HahnSeries.single (1 : ℤ) 1) -
      HahnSeries.single (1 : ℤ) 1).orderTop =
        ((ℓ + ((p - 1 : ℕ) : ℤ) * d : ℤ) : WithTop ℤ) ∧
      ℓ + ((p - 1 : ℕ) : ℤ) * d - 1 < ((p : ℤ) + 1) * d := by
  let N := substitutionDifference g hG
  let E := g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α - HahnSeries.single ℓ β
  let L := ℓ + ((p - 1 : ℕ) : ℤ) * d
  let b := β * ∏ i ∈ Finset.range (p - 1), (((ℓ + (i : ℤ) * d : ℤ) : k) * α)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have hp2 : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by omega
  have hfirst : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2) := orderAddSubgroup_antitone hlo
    (mem_orderAddSubgroup_of_sub_single_mem _ ℓ β hg)
  have hδ : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
    mem_orderAddSubgroup_of_sub_single_mem _ (d + 1) α
      (orderAddSubgroup_antitone (by omega) hfirst)
  have hAone := substitutionDifference_divisible_monomial_mem p g hG d hd hδ hdp α
  have hAn := substitutionDifference_pow_mem g hG d hd hδ (p - 2)
    (((p : ℤ) + 1) * d + 1) (N (HahnSeries.single (d + 1) α)) hAone
  have hA : (N ^ (p - 1)) (HahnSeries.single (d + 1) α) ∈ orderAddSubgroup (L + 1) := by
    have heq : N ^ (p - 1) = N ^ (p - 2) * N := by
      rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
    rw [heq, Module.End.mul_apply]
    apply orderAddSubgroup_antitone _ hAn
    dsimp only [L]
    rw [hp1, hp2]
    nlinarith
  have hB := substitutionDifference_pow_leadingTerm_mem g hG d hd α hfirst
    (HahnSeries.single ℓ β) ℓ β (by simp) (p - 1)
  change (N ^ (p - 1)) (HahnSeries.single ℓ β) - HahnSeries.single L b ∈
    orderAddSubgroup (L + 1) at hB
  have hEn := substitutionDifference_pow_mem g hG d hd hδ (p - 1) (ℓ + 1) E hg
  have hE : (N ^ (p - 1)) E ∈ orderAddSubgroup (L + 1) := by
    simpa only [L, add_right_comm] using hEn
  have hinit : N (HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.single (d + 1) α + HahnSeries.single ℓ β + E := by
    dsimp only [N, E]
    rw [substitutionDifference_apply, subst_X]
    ring
  have hpower : N ^ p = N ^ (p - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hres : (N ^ p) (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single L b ∈
      orderAddSubgroup (L + 1) := by
    rw [hpower, Module.End.mul_apply, hinit, map_add, map_add]
    convert (orderAddSubgroup (L + 1)).add_mem
      ((orderAddSubgroup (L + 1)).add_mem hA hB) hE using 1
    ring
  change (substitutionDifference g hG ^ p) _ - _ ∈ _ at hres
  rw [substitutionDifference_pow_char p g hG] at hres
  have hb : b ≠ 0 := mul_ne_zero hβ (resonantLeadingProduct_ne_zero p d ℓ hdp hℓp α hα)
  have hc := (mem_orderAddSubgroup_iff_coeff (L + 1) _).mp hres L (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  have hcoeff : ((subst 0 IsNilpotent.zero g hG)^[p] (HahnSeries.single (1 : ℤ) 1) -
      HahnSeries.single (1 : ℤ) 1).coeff L ≠ 0 := by rw [hc]; exact hb
  refine ⟨le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hcoeff)
    (mem_orderAddSubgroup_of_sub_single_mem _ L b hres), ?_⟩
  rw [hp1]
  nlinarith

/-- A single actual higher-degree coordinate change in the original
power-series ring. -/
def elementaryCoordinate (q : ℕ) (t : k) : PowerSeries k :=
  PowerSeries.X + PowerSeries.monomial q t

@[simp]
theorem constantCoeff_elementaryCoordinate (q : ℕ) (hq : 2 ≤ q) (t : k) :
    (elementaryCoordinate q t).constantCoeff = 0 := by
  have hm : PowerSeries.constantCoeff (PowerSeries.monomial q t) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial,
      ite_eq_right (by omega)]
  simpa only [elementaryCoordinate, map_add, PowerSeries.constantCoeff_X, zero_add] using hm

@[simp]
theorem coeff_one_elementaryCoordinate (q : ℕ) (hq : 2 ≤ q) (t : k) :
    (elementaryCoordinate q t).coeff 1 = 1 := by
  simp [elementaryCoordinate, PowerSeries.coeff_monomial, show (1 : ℕ) ≠ q by omega]

/-- The actual elementary coordinate has unit linear coefficient. -/
theorem elementaryCoordinate_isUnit_linear (q : ℕ) (hq : 2 ≤ q) (t : k) :
    IsUnit ((elementaryCoordinate q t).coeff 1) := by
  rw [coeff_one_elementaryCoordinate q hq t]
  exact isUnit_one

/-- A power-series monomial embeds as the same canonical Laurent monomial. -/
theorem ofPowerSeries_monomial (q : ℕ) (t : k) :
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.monomial q t) = HahnSeries.single (q : ℤ) t := by
  ext j
  cases j with
  | ofNat n => simp [PowerSeries.coeff_coe, PowerSeries.coeff_monomial, HahnSeries.coeff_single]
  | negSucc n =>
    rw [PowerSeries.coeff_coe, ite_eq_left (Int.negSucc_lt_zero n),
      HahnSeries.coeff_single_of_ne (by omega)]

/-- The elementary coordinate is the actual variable plus its stated
single Laurent monomial. -/
theorem ofPowerSeries_elementaryCoordinate (q : ℕ) (t : k) :
    HahnSeries.ofPowerSeries ℤ k (elementaryCoordinate q t) =
      HahnSeries.single (1 : ℤ) 1 + HahnSeries.single (q : ℤ) t := by
  rw [elementaryCoordinate, map_add, HahnSeries.ofPowerSeries_X, ofPowerSeries_monomial]

/-- Every original support bound is preserved by the actual inverse
power-series coordinate, including zero series. -/
theorem powerSeriesSubstEquiv_symm_mem_iff (w : PowerSeries k) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) (m : ℤ) (x : LaurentSeries k) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm x ∈ orderAddSubgroup m ↔
      x ∈ orderAddSubgroup m := by
  simp only [mem_orderAddSubgroup, orderTop_powerSeriesSubstEquiv_symm]

/-- The actual elementary conjugation changes precisely the stated
coefficient, with a proved higher tail. The formula uses integer subtraction
before casting; no integer equality is confused with a congruence. -/
theorem elementary_conjugate_leadingTerm_mem (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (d : ℤ) (hd : 1 ≤ d) (q : ℕ) (hq : 2 ≤ q) (α β t : k)
    (hg : HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α - HahnSeries.single (d + (q : ℤ)) β ∈
        orderAddSubgroup (d + (q : ℤ) + 1)) :
    HahnSeries.ofPowerSeries ℤ k
        (powerSeriesConjugate f (elementaryCoordinate q t) (elementaryCoordinate_isUnit_linear q hq t)) -
      HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α -
      HahnSeries.single (d + (q : ℤ))
        (β + t * (((q : ℤ) - 1 - d : ℤ) : k) * α) ∈
          orderAddSubgroup (d + (q : ℤ) + 1) := by
  let g := HahnSeries.ofPowerSeries ℤ k f
  let hG := isAdmissible_ofPowerSeries 0 f hf hflinear
  let F := subst 0 IsNilpotent.zero g hG
  let w := elementaryCoordinate q t
  have hw : w.constantCoeff = 0 := constantCoeff_elementaryCoordinate q hq t
  have hwlinear : IsUnit (w.coeff 1) := elementaryCoordinate_isUnit_linear q hq t
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  let A := F (HahnSeries.ofPowerSeries ℤ k w) - HahnSeries.ofPowerSeries ℤ k w
  let ℓ := d + (q : ℤ)
  let γ := β + t * (((q : ℤ) - 1 - d : ℤ) : k) * α
  have hfirst : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2) := orderAddSubgroup_antitone (by dsimp only [ℓ]; omega)
    (mem_orderAddSubgroup_of_sub_single_mem _ ℓ β hg)
  have hmono := subst_sub_leadingTerm_mem g hG d hd α hfirst
    (HahnSeries.single (q : ℤ) t) (q : ℤ) t (by simp)
  have hmono' : F (HahnSeries.single (q : ℤ) t) - HahnSeries.single (q : ℤ) t -
      HahnSeries.single ℓ ((((q : ℤ) : k) * α) * t) ∈ orderAddSubgroup (ℓ + 1) := by
    simpa only [F, ℓ, add_comm, add_left_comm, add_assoc] using hmono
  have hA : A - HahnSeries.single (d + 1) α -
      HahnSeries.single ℓ (β + (((q : ℤ) : k) * α) * t) ∈ orderAddSubgroup (ℓ + 1) := by
    convert (orderAddSubgroup (ℓ + 1)).add_mem hg hmono' using 1
    dsimp only [A, F, w, g, ℓ]
    rw [ofPowerSeries_elementaryCoordinate, map_add, subst_X, HahnSeries.single_add]
    ring
  have hwexp : HahnSeries.ofPowerSeries ℤ k w - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single ((q : ℤ) - 1 + 1) t ∈ orderAddSubgroup ((q : ℤ) - 1 + 2) := by
    simp only [w, ofPowerSeries_elementaryCoordinate, sub_add_cancel, add_sub_cancel_left,
      sub_self, zero_mem]
  have hEa := subst_sub_leadingTerm_mem (HahnSeries.ofPowerSeries ℤ k w)
    (isAdmissible_ofPowerSeries 0 w hw hwlinear) ((q : ℤ) - 1) (by omega) t hwexp
    (HahnSeries.single (d + 1) α) (d + 1) α (by simp)
  have hEa' : E (HahnSeries.single (d + 1) α) - HahnSeries.single (d + 1) α -
      HahnSeries.single ℓ ((((d + 1 : ℤ) : k) * t) * α) ∈ orderAddSubgroup (ℓ + 1) := by
    simpa only [E, powerSeriesSubstEquiv_apply, ℓ,
      show d + 1 + ((q : ℤ) - 1) = d + (q : ℤ) by omega] using hEa
  have hwδ : HahnSeries.ofPowerSeries ℤ k w - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup ((q : ℤ) - 1 + 1) :=
    mem_orderAddSubgroup_of_sub_single_mem _ ((q : ℤ) - 1 + 1) t
      (by simpa only [sub_add_cancel] using
        (orderAddSubgroup_antitone (show (q : ℤ) + 1 ≤ (q : ℤ) - 1 + 2 by omega) hwexp))
  have hEb := subst_sub_mem_orderAddSubgroup (HahnSeries.ofPowerSeries ℤ k w)
    (isAdmissible_ofPowerSeries 0 w hw hwlinear) ((q : ℤ) - 1) (by omega) hwδ
    ℓ (HahnSeries.single ℓ γ) HahnSeries.orderTop_single_le
  have hEb' : E (HahnSeries.single ℓ γ) - HahnSeries.single ℓ γ ∈ orderAddSubgroup (ℓ + 1) :=
    orderAddSubgroup_antitone (by omega) hEb
  have hγ : β + (((q : ℤ) : k) * α) * t = (((d + 1 : ℤ) : k) * t) * α + γ := by
    dsimp only [γ]
    push_cast
    ring
  have hR : A - E (HahnSeries.single (d + 1) α) - E (HahnSeries.single ℓ γ) ∈
      orderAddSubgroup (ℓ + 1) := by
    convert (orderAddSubgroup (ℓ + 1)).sub_mem
      ((orderAddSubgroup (ℓ + 1)).sub_mem hA hEa') hEb' using 1
    rw [hγ]
    simp only [HahnSeries.single_add]
    abel
  rw [powerSeriesConjugate_sub_variable f w hf hflinear hw hwlinear]
  change E.symm A - HahnSeries.single (d + 1) α - HahnSeries.single ℓ γ ∈ orderAddSubgroup (ℓ + 1)
  have hi := (powerSeriesSubstEquiv_symm_mem_iff w hw hwlinear (ℓ + 1)
    (A - E (HahnSeries.single (d + 1) α) - E (HahnSeries.single ℓ γ))).mpr hR
  simpa only [E, map_sub, AlgEquiv.symm_apply_apply] using hi

/-- The nonresonant coefficient has a unique cancelling coordinate
parameter. Its denominator is proved nonzero in the original coefficient field. -/
theorem existsUnique_elementary_coefficient_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    (d : ℤ) (hdp : (p : ℤ) ∣ d + 1) (q : ℕ) (hpq : ¬p ∣ q)
    (α β : k) (hα : α ≠ 0) :
    ∃! t : k, β + t * (((q : ℤ) - 1 - d : ℤ) : k) * α = 0 := by
  have hdcast : ((d + 1 : ℤ) : k) = 0 := by
    obtain ⟨n, hn⟩ := hdp
    rw [hn, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero k p, zero_mul]
  have hcast : (((q : ℤ) - 1 - d : ℤ) : k) = (q : k) := by
    push_cast at hdcast ⊢
    linear_combination -hdcast
  let a := (q : k) * α
  have ha : a ≠ 0 := mul_ne_zero ((CharP.cast_eq_zero_iff k p q).not.mpr hpq) hα
  let t := -β / a
  have ht : β + t * a = 0 := by
    dsimp only [t]
    rw [div_mul_cancel₀ _ ha, add_neg_cancel]
  refine ⟨t, ?_, ?_⟩
  · change β + t * (((q : ℤ) - 1 - d : ℤ) : k) * α = 0
    rw [hcast, mul_assoc]
    exact ht
  · intro s hs
    change β + s * (((q : ℤ) - 1 - d : ℤ) : k) * α = 0 at hs
    rw [hcast, mul_assoc] at hs
    apply mul_right_cancel₀ ha
    linear_combination hs - ht

/-- An actual elementary coordinate removes the nonresonant coefficient
and preserves every earlier term of the displayed Laurent expansion. -/
theorem exists_elementary_conjugate_remove (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (d : ℤ) (hd : 1 ≤ d) (hdp : (p : ℤ) ∣ d + 1)
    (q : ℕ) (hq : 2 ≤ q) (hpq : ¬p ∣ q) (α β : k) (hα : α ≠ 0)
    (hg : HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α - HahnSeries.single (d + (q : ℤ)) β ∈
        orderAddSubgroup (d + (q : ℤ) + 1)) :
    ∃ t : k, HahnSeries.ofPowerSeries ℤ k
        (powerSeriesConjugate f (elementaryCoordinate q t) (elementaryCoordinate_isUnit_linear q hq t)) -
      HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
        orderAddSubgroup (d + (q : ℤ) + 1) := by
  obtain ⟨t, ht, _⟩ := existsUnique_elementary_coefficient_zero p d hdp q hpq α β hα
  refine ⟨t, ?_⟩
  have h := elementary_conjugate_leadingTerm_mem f hf hflinear d hd q hq α β t hg
  simpa only [ht, HahnSeries.single_eq_zero, sub_zero] using h

/-- Actual composition of zero-constant power series is zero-constant. -/
theorem constantCoeff_powerSeries_subst (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hw : w.constantCoeff = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst f w) = 0 := by
  simpa only [PowerSeries.constantCoeff_eq] using PowerSeries.constantCoeff_subst_eq_zero hf w hw

/-- Unit linear coefficients are preserved by actual composition. -/
theorem isUnit_linear_powerSeries_subst (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hwlinear : IsUnit (w.coeff 1)) : IsUnit (PowerSeries.coeff 1 (PowerSeries.subst f w)) := by
  rw [coeff_one_powerSeries_subst f w hf]
  exact hwlinear.mul hflinear

/-- Unit linear coefficients are preserved by the actual coordinate conjugate. -/
theorem isUnit_linear_powerSeriesConjugate (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    IsUnit ((powerSeriesConjugate f w hwlinear).coeff 1) := by
  rw [coeff_one_powerSeriesConjugate f w hf hw hwlinear]
  exact hflinear

/-- Actual composition of power-series coordinates gives the corresponding
composition of the canonical Laurent automorphisms. Continuity supplies the
necessary homomorphism uniqueness. -/
theorem powerSeriesSubstEquiv_subst (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero (PowerSeries.subst f w)
        (constantCoeff_powerSeries_subst f w hf hw)
        (isUnit_linear_powerSeries_subst f w hf hflinear hwlinear) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).trans
        (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear) := by
  let := orderTopology k
  let C := (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).trans
    (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)
  have hX : C (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k (PowerSeries.subst f w) := by
    change powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
      (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear (HahnSeries.single (1 : ℤ) 1)) = _
    rw [show powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
      (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k w from subst_X 0 IsNilpotent.zero _ _]
    rw [powerSeriesSubstEquiv_apply,
      subst_ofPowerSeries 0 IsNilpotent.zero f hf hflinear w]
  have hC := (continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear).comp
    (continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear)
  have heq := subst_unique 0 IsNilpotent.zero _
    (isAdmissible_ofPowerSeries 0 (PowerSeries.subst f w)
      (constantCoeff_powerSeries_subst f w hf hw)
      (isUnit_linear_powerSeries_subst f w hf hflinear hwlinear)) C.toAlgHom hC hX
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun heq.symm x

/-- The actual coordinate conjugate has the genuinely conjugated canonical
substitution automorphism, established with continuous homomorphism uniqueness. -/
theorem powerSeriesSubstEquiv_powerSeriesConjugate (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesConjugate f w hwlinear)
        (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
        (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear) =
      ((powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).trans
        (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)).trans
          (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm := by
  let := orderTopology k
  let W := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  let F := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
  let C := (W.trans F).trans W.symm
  have hX : C (HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) := by
    change W.symm (F (W (HahnSeries.single (1 : ℤ) 1))) = _
    rw [show W (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k w from
      subst_X 0 IsNilpotent.zero _ _]
    exact (ofPowerSeries_powerSeriesConjugate f w hf hflinear hw hwlinear).symm
  have hC := (continuous_powerSeriesSubstEquiv_symm 0 IsNilpotent.zero w hw hwlinear).comp
    ((continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear).comp
      (continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear))
  have heq := subst_unique 0 IsNilpotent.zero _
    (isAdmissible_ofPowerSeries 0 (powerSeriesConjugate f w hwlinear)
      (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
      (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear)) C.toAlgHom hC hX
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun heq.symm x

/-- The actual iterated power-series substitution of the variable. -/
def powerSeriesIterate (f : PowerSeries k) (n : ℕ) : PowerSeries k :=
  (PowerSeries.subst f : PowerSeries k → PowerSeries k)^[n] PowerSeries.X

@[simp]
theorem powerSeriesIterate_zero (f : PowerSeries k) : powerSeriesIterate f 0 = PowerSeries.X := rfl

theorem powerSeriesIterate_succ (f : PowerSeries k) (n : ℕ) :
    powerSeriesIterate f (n + 1) = PowerSeries.subst f (powerSeriesIterate f n) := by
  simp only [powerSeriesIterate, Function.iterate_succ_apply']

/-- The actual iterates retain zero constant and the expected linear coefficient. -/
theorem powerSeriesIterate_spec (f : PowerSeries k) (hf : f.constantCoeff = 0) (n : ℕ) :
    (powerSeriesIterate f n).constantCoeff = 0 ∧ (powerSeriesIterate f n).coeff 1 = f.coeff 1 ^ n := by
  induction n with
  | zero => simp only [powerSeriesIterate_zero, PowerSeries.constantCoeff_X, PowerSeries.coeff_X,
      ite_true, pow_zero, and_self]
  | succ n ih =>
    rw [powerSeriesIterate_succ]
    refine ⟨constantCoeff_powerSeries_subst f _ hf ih.1, ?_⟩
    rw [coeff_one_powerSeries_subst f _ hf, ih.2, pow_succ]

/-- The actual Laurent substitution and ordinary power-series substitution
have the same iterates on every power-series input. -/
theorem ofPowerSeries_iterate_subst (f : PowerSeries k) (hf : f.constantCoeff = 0)
    (hflinear : IsUnit (f.coeff 1)) (n : ℕ) (w : PowerSeries k) :
    HahnSeries.ofPowerSeries ℤ k ((PowerSeries.subst f : PowerSeries k → PowerSeries k)^[n] w) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[n]
        (HahnSeries.ofPowerSeries ℤ k w) := by
  have h : Function.Semiconj (HahnSeries.ofPowerSeries ℤ k)
      (PowerSeries.subst f : PowerSeries k → PowerSeries k)
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear) := by
    intro P
    exact (subst_ofPowerSeries 0 IsNilpotent.zero f hf hflinear P).symm
  exact h.iterate_right n w

/-- The original power-series iterate is exactly the actual Laurent
substitution iterate of the variable. -/
theorem ofPowerSeries_powerSeriesIterate (f : PowerSeries k) (hf : f.constantCoeff = 0)
    (hflinear : IsUnit (f.coeff 1)) (n : ℕ) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f n) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[n]
        (HahnSeries.single (1 : ℤ) 1) := by
  simpa only [powerSeriesIterate, HahnSeries.ofPowerSeries_X] using
    ofPowerSeries_iterate_subst f hf hflinear n PowerSeries.X

/-- Associativity identifies substitution at the actual iterated parameter
with the repeated original substitution on every power series. -/
theorem powerSeries_subst_iterate_eq (f : PowerSeries k) (hf : f.constantCoeff = 0)
    (n : ℕ) (w : PowerSeries k) :
    PowerSeries.subst (powerSeriesIterate f n) w =
      (PowerSeries.subst f : PowerSeries k → PowerSeries k)^[n] w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [powerSeriesIterate_succ,
      ← PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' (powerSeriesIterate_spec f hf n).1)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hf) w,
      ih, Function.iterate_succ_apply']

/-- On power-series inputs, the canonical automorphism at the actual iterate
is the actual iterated automorphism. -/
theorem powerSeriesSubstEquiv_iterate_ofPowerSeries (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1)) (n : ℕ) (w : PowerSeries k) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesIterate f n)
        (powerSeriesIterate_spec f hf n).1
        (by rw [(powerSeriesIterate_spec f hf n).2]; exact hflinear.pow n)
        (HahnSeries.ofPowerSeries ℤ k w) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[n]
        (HahnSeries.ofPowerSeries ℤ k w) := by
  rw [powerSeriesSubstEquiv_apply,
    subst_ofPowerSeries 0 IsNilpotent.zero _ (powerSeriesIterate_spec f hf n).1
      (by rw [(powerSeriesIterate_spec f hf n).2]; exact hflinear.pow n),
    powerSeries_subst_iterate_eq f hf n w]
  exact ofPowerSeries_iterate_subst f hf hflinear n w

/-- Actual coordinate conjugation commutes with every actual substitution
iterate, by the canonical semiconjugacy theorem. -/
theorem iterate_powerSeriesSubstEquiv_conjugate_apply (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) (n : ℕ) (x : LaurentSeries k) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesConjugate f w hwlinear)
      (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
      (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear))^[n] x =
    (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm
      ((powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[n]
        (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear x)) := by
  let W := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  let F := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
  let C := powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesConjugate f w hwlinear)
    (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
    (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear)
  have hs : Function.Semiconj W C F := by
    intro y
    dsimp only [C]
    rw [powerSeriesSubstEquiv_powerSeriesConjugate f w hf hflinear hw hwlinear]
    change W (W.symm (F (W y))) = F (W y)
    exact W.apply_symm_apply _
  have h := congrArg W.symm (hs.iterate_right n x)
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- The displacement order of every iterate is invariant under the actual
coordinate, including an iterate equal to the identity. -/
theorem orderTop_iterate_powerSeriesConjugate_sub_variable (f w : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) (n : ℕ) :
    ((powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesConjugate f w hwlinear)
      (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
      (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear))^[n]
        (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1).orderTop =
    ((powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[n]
        (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1).orderTop := by
  have hfn := powerSeriesIterate_spec f hf n
  have hfnlinear : IsUnit ((powerSeriesIterate f n).coeff 1) := by rw [hfn.2]; exact hflinear.pow n
  rw [iterate_powerSeriesSubstEquiv_conjugate_apply f w hf hflinear hw hwlinear n,
    show powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
      (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k w from subst_X 0 IsNilpotent.zero _ _,
    ← powerSeriesSubstEquiv_iterate_ofPowerSeries f hf hflinear n w,
    ← ofPowerSeries_powerSeriesConjugate (powerSeriesIterate f n) w hfn.1 hfnlinear hw hwlinear,
    orderTop_powerSeriesConjugate_sub_variable (powerSeriesIterate f n) w hfn.1 hfnlinear hw hwlinear,
    ofPowerSeries_powerSeriesIterate f hf hflinear n]

/-- Successive actual coordinate changes compose as the original power
series. The equality is derived from their canonical automorphisms. -/
theorem powerSeriesConjugate_powerSeriesConjugate (f w v : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1))
    (hv : v.constantCoeff = 0) (hvlinear : IsUnit (v.coeff 1)) :
    powerSeriesConjugate (powerSeriesConjugate f w hwlinear) v hvlinear =
      powerSeriesConjugate f (PowerSeries.subst w v)
        (isUnit_linear_powerSeries_subst w v hw hwlinear hvlinear) := by
  let W := powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear
  let V := powerSeriesSubstEquiv 0 IsNilpotent.zero v hv hvlinear
  let F := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
  have heq : HahnSeries.ofPowerSeries ℤ k
      (powerSeriesConjugate (powerSeriesConjugate f w hwlinear) v hvlinear) =
      HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f (PowerSeries.subst w v)
        (isUnit_linear_powerSeries_subst w v hw hwlinear hvlinear)) := by
    rw [ofPowerSeries_powerSeriesConjugate _ v
      (constantCoeff_powerSeriesConjugate f w hf hw hwlinear)
      (isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear) hv hvlinear,
      powerSeriesSubstEquiv_powerSeriesConjugate f w hf hflinear hw hwlinear,
      ofPowerSeries_powerSeriesConjugate f (PowerSeries.subst w v) hf hflinear
        (constantCoeff_powerSeries_subst w v hw hv)
        (isUnit_linear_powerSeries_subst w v hw hwlinear hvlinear),
      powerSeriesSubstEquiv_subst w v hw hwlinear hv hvlinear]
    change V.symm (W.symm (F (W (HahnSeries.ofPowerSeries ℤ k v)))) =
      V.symm (W.symm (F (HahnSeries.ofPowerSeries ℤ k (PowerSeries.subst w v))))
    rw [show W (HahnSeries.ofPowerSeries ℤ k v) =
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.subst w v) from
        subst_ofPowerSeries 0 IsNilpotent.zero w hw hwlinear v]
  ext n
  simpa only [HahnSeries.ofPowerSeries_apply_coeff] using
    congrArg (fun x : LaurentSeries k ↦ x.coeff (n : ℤ)) heq

/-- The identity coordinate gives the original power series. -/
theorem powerSeriesConjugate_X (f : PowerSeries k) (hf : f.constantCoeff = 0) :
    powerSeriesConjugate f PowerSeries.X (by simp) = f := by
  have hi : (PowerSeries.X : PowerSeries k).substInvOfIsUnit (by simp) = PowerSeries.X := by
    simpa using PowerSeries.subst_substInvOfIsUnit_left (PowerSeries.X : PowerSeries k) (by simp) (by simp)
  simp only [powerSeriesConjugate, hi]
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hf)]
  simp

/-- Removing the coefficient at any given lower support bound raises that
bound by one, including when the input or that coefficient is zero. -/
theorem sub_coeff_mem_orderAddSubgroup_succ (x : LaurentSeries k) (m : ℤ)
    (hx : x ∈ orderAddSubgroup m) :
    x - HahnSeries.single m (x.coeff m) ∈ orderAddSubgroup (m + 1) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sub]
  by_cases hjm : j = m
  · subst j
    rw [HahnSeries.coeff_single_same, sub_self]
  · rw [(mem_orderAddSubgroup_iff_coeff m x).mp hx j (by omega),
      HahnSeries.coeff_single_of_ne hjm, sub_self]

/-- The actual normal form controlled by the next ramification number.
The hypothesis on the next iterate is a support bound on the actual iterate;
an identity iterate is therefore included. Each coordinate is constructed by
the finite elimination, not supplied as an extra existence certificate. -/
theorem exists_powerSeries_normalForm (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (d : ℤ) (hd : 1 ≤ d) (hdp : (p : ℤ) ∣ d + 1)
    (hfinite : (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).orderTop =
      ((d + 1 : ℤ) : WithTop ℤ))
    (hnext : (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear)^[p]
      (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈
        orderAddSubgroup (((p : ℤ) + 1) * d + 1)) :
    ∃ (w : PowerSeries k) (_hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) (α : k),
      α ≠ 0 ∧ HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) -
        HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1) := by
  let δ := HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1
  have hδne : δ ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hfinite]; exact WithTop.coe_ne_top)
  have hδorder : δ.order = d + 1 := by
    exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hδne).trans hfinite
  let α := δ.coeff (d + 1)
  have hα : α ≠ 0 := by
    dsimp only [α]
    rw [← hδorder]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hδne
  have hfirst : δ - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + 2) := by
    simpa only [hδorder, α, show d + 1 + 1 = d + 2 by omega] using sub_leadingTerm_mem_orderAddSubgroup δ
  have hdNat : (d.toNat : ℤ) = d := by omega
  have aux : ∀ n : ℕ, n ≤ d.toNat - 1 →
      ∃ (w : PowerSeries k) (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)),
        HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate f w hwlinear) -
          HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
            orderAddSubgroup (d + 2 + (n : ℤ)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨PowerSeries.X, by simp, by simp, ?_⟩
      simpa only [powerSeriesConjugate_X f hf, Nat.cast_zero, add_zero] using hfirst
    | succ n ih =>
      intro hn
      obtain ⟨w, hw, hwlinear, hg⟩ := ih (by omega)
      let g := powerSeriesConjugate f w hwlinear
      have hg0 : g.constantCoeff = 0 := constantCoeff_powerSeriesConjugate f w hf hw hwlinear
      have hglinear : IsUnit (g.coeff 1) := isUnit_linear_powerSeriesConjugate f w hf hflinear hw hwlinear
      let ℓ := d + 2 + (n : ℤ)
      let R := HahnSeries.ofPowerSeries ℤ k g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α
      let β := R.coeff ℓ
      have hR : R ∈ orderAddSubgroup ℓ := hg
      have htail := sub_coeff_mem_orderAddSubgroup_succ R ℓ hR
      change R - HahnSeries.single ℓ β ∈ orderAddSubgroup (ℓ + 1) at htail
      have hidx : ℓ + 1 = d + 2 + ((n + 1 : ℕ) : ℤ) := by dsimp only [ℓ]; push_cast; ring
      by_cases hβ : β = 0
      · refine ⟨w, hw, hwlinear, ?_⟩
        simpa only [hβ, HahnSeries.single_eq_zero, sub_zero, hidx] using htail
      · let q := n + 2
        have hq : 2 ≤ q := by dsimp only [q]; omega
        have hℓ : ℓ = d + (q : ℤ) := by dsimp only [ℓ, q]; push_cast; ring
        have hpq : ¬p ∣ q := by
          intro hpq
          have hpqZ : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpq
          have hℓp : (p : ℤ) ∣ ℓ + 1 := by
            rw [show ℓ + 1 = (d + 1) + (q : ℤ) by rw [hℓ]; ring]
            exact dvd_add hdp hpqZ
          have hr := resonant_iterate_orderTop p (HahnSeries.ofPowerSeries ℤ k g)
            (isAdmissible_ofPowerSeries 0 g hg0 hglinear) d ℓ hd
            (by dsimp only [ℓ]; omega) (by dsimp only [ℓ]; omega)
            hdp hℓp α β hα hβ htail
          have hbound : (((p : ℤ) + 1) * d + 1 : ℤ) ≤ ℓ + ((p - 1 : ℕ) : ℤ) * d := by
            have hc : (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0 hglinear)^[p]
                (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈
                  orderAddSubgroup (((p : ℤ) + 1) * d + 1) := by
              change ((((p : ℤ) + 1) * d + 1 : ℤ) : WithTop ℤ) ≤ _
              rw [orderTop_iterate_powerSeriesConjugate_sub_variable f w hf hflinear hw hwlinear p]
              exact hnext
            change ((((p : ℤ) + 1) * d + 1 : ℤ) : WithTop ℤ) ≤
              ((subst 0 IsNilpotent.zero (HahnSeries.ofPowerSeries ℤ k g)
                (isAdmissible_ofPowerSeries 0 g hg0 hglinear))^[p]
                  (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1).orderTop at hc
            rw [hr.1] at hc
            exact WithTop.coe_le_coe.mp hc
          have hsmall := hr.2
          omega
        have htailq : HahnSeries.ofPowerSeries ℤ k g - HahnSeries.single (1 : ℤ) 1 -
            HahnSeries.single (d + 1) α - HahnSeries.single (d + (q : ℤ)) β ∈
              orderAddSubgroup (d + (q : ℤ) + 1) := by rw [← hℓ]; exact htail
        obtain ⟨t, ht⟩ := exists_elementary_conjugate_remove p g hg0 hglinear d hd hdp q hq hpq α β hα htailq
        let v := elementaryCoordinate q t
        have hv : v.constantCoeff = 0 := constantCoeff_elementaryCoordinate q hq t
        have hvlinear : IsUnit (v.coeff 1) := elementaryCoordinate_isUnit_linear q hq t
        refine ⟨PowerSeries.subst w v, constantCoeff_powerSeries_subst w v hw hv,
          isUnit_linear_powerSeries_subst w v hw hwlinear hvlinear, ?_⟩
        rw [← powerSeriesConjugate_powerSeriesConjugate f w v hf hflinear hw hwlinear hv hvlinear]
        have hi : d + (q : ℤ) + 1 = d + 2 + ((n + 1 : ℕ) : ℤ) := by dsimp only [q]; push_cast; ring
        simpa only [hi] using ht
  obtain ⟨w, hw, hwlinear, ht⟩ := aux (d.toNat - 1) le_rfl
  refine ⟨w, hw, hwlinear, α, hα, ?_⟩
  have hi : d + 2 + ((d.toNat - 1 : ℕ) : ℤ) = 2 * d + 1 := by omega
  simpa only [hi] using ht

/-- The normal form directly on the original Laurent carrier. Positive
support, admissibility and the power-series coordinate are derived from the
actual finite displacement order, so residue Laurent inputs require no extra
representation or coordinate-existence assumption. -/
theorem exists_laurent_normalForm (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (d : ℤ) (hd : 1 ≤ d) (hdp : (p : ℤ) ∣ d + 1)
    (hfinite : (g - HahnSeries.single (1 : ℤ) 1).orderTop = ((d + 1 : ℤ) : WithTop ℤ))
    (hnext : (subst 0 IsNilpotent.zero g
      (isAdmissible_of_sub_variable_mem g d hd hfinite.ge))^[p]
        (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈
          orderAddSubgroup (((p : ℤ) + 1) * d + 1)) :
    ∃ (w : PowerSeries k) (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) (α : k),
      α ≠ 0 ∧ (powerSeriesSubstEquiv 0 IsNilpotent.zero w hw hwlinear).symm
        (subst 0 IsNilpotent.zero g (isAdmissible_of_sub_variable_mem g d hd hfinite.ge)
          (HahnSeries.ofPowerSeries ℤ k w)) - HahnSeries.single (1 : ℤ) 1 -
          HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1) := by
  have hδ : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) := hfinite.ge
  have hg1 : g ∈ orderAddSubgroup 1 := by
    simpa only [sub_add_cancel] using (orderAddSubgroup 1).add_mem
      (orderAddSubgroup_antitone (show 1 ≤ d + 1 by omega) hδ)
      (show HahnSeries.single (1 : ℤ) (1 : k) ∈ orderAddSubgroup 1 from HahnSeries.orderTop_single_le)
  let P := PowerSeries.mk (fun n : ℕ ↦ g.coeff (n : ℤ))
  have hP : HahnSeries.ofPowerSeries ℤ k P = g :=
    ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero g
      (orderAddSubgroup_antitone (show (0 : ℤ) ≤ 1 by omega) hg1)
  have hP0 : P.constantCoeff = 0 := by
    simpa only [P, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      Nat.cast_zero] using (mem_orderAddSubgroup_iff_coeff 1 g).mp hg1 0 (by omega)
  have hc := (mem_orderAddSubgroup_iff_coeff (d + 1) _).mp hδ 1 (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  have hP1 : P.coeff 1 = 1 := by simpa only [P, PowerSeries.coeff_mk, Nat.cast_one] using hc
  have hPlinear : IsUnit (P.coeff 1) := by rw [hP1]; exact isUnit_one
  have hmap : (powerSeriesSubstEquiv 0 IsNilpotent.zero P hP0 hPlinear :
      LaurentSeries k → LaurentSeries k) =
      subst 0 IsNilpotent.zero g (isAdmissible_of_sub_variable_mem g d hd hfinite.ge) := by
    funext x
    rw [powerSeriesSubstEquiv_apply]
    simp only [hP]
  have hnextP : (powerSeriesSubstEquiv 0 IsNilpotent.zero P hP0 hPlinear)^[p]
      (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈
        orderAddSubgroup (((p : ℤ) + 1) * d + 1) := by
    rw [hmap]
    exact hnext
  obtain ⟨w, hw, hwlinear, α, hα, ht⟩ := exists_powerSeries_normalForm p P hP0 hPlinear d hd hdp
    (by rw [hP]; exact hfinite) hnextP
  refine ⟨w, hw, hwlinear, α, hα, ?_⟩
  rw [ofPowerSeries_powerSeriesConjugate P w hP0 hPlinear hw hwlinear,
    powerSeriesSubstEquiv_apply] at ht
  simpa only [hP] using ht

end LaurentSeries
