module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.PowerSeries.PrincipalUnitPowers

/-!
# Exact invariant differentials from weighted substitution identities

The two weighted identities in Yuan, Section 6, equations (6.1), produce
an actual nonzero exact invariant differential. Signed Laurent orders and
the original leading scalar are retained throughout the normalization.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

open FalseTateNonliftability.CoefficientRing

variable {k : Type*} [Field k]

local instance invariantDifferentialZeroSpanIsMaximal :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

private theorem leadingCoeff_ofPowerSeries_of_constantCoeff_ne_zero
    (P : PowerSeries k) (hP : P.constantCoeff ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ k P).leadingCoeff = P.constantCoeff := by
  have hunit : IsUnit P := PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr hP)
  have hne : HahnSeries.ofPowerSeries ℤ k P ≠ 0 :=
    (hunit.map (HahnSeries.ofPowerSeries ℤ k)).ne_zero
  have htop : (HahnSeries.ofPowerSeries ℤ k P).orderTop = 0 := by
    rw [HahnSeries.orderTop_ofPowerSeries, PowerSeries.order_zero_of_isUnit hunit]
    rfl
  have ho : (HahnSeries.ofPowerSeries ℤ k P).order = 0 := by
    exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hne).trans htop
  rw [HahnSeries.leadingCoeff_eq, ho]
  simpa using HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) P 0

/-- A genuine coordinate substitution multiplies the leading coefficient by
the linear coefficient to the signed original Laurent order. -/
theorem leadingCoeff_powerSeriesSubstEquiv (g : PowerSeries k)
    (hg : g.constantCoeff = 0) (hlinear : IsUnit (g.coeff 1))
    (x : LaurentSeries k) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear x).leadingCoeff =
      g.coeff 1 ^ x.order * x.leadingCoeff := by
  let E := powerSeriesSubstEquiv (0 : k) IsNilpotent.zero g hg hlinear
  have hX : E (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k g :=
    subst_X 0 IsNilpotent.zero _ _
  have ho : (HahnSeries.ofPowerSeries ℤ k g).order = 1 := by
    have h := order_powerSeriesSubstEquiv g hg hlinear (HahnSeries.single 1 1)
    change (E (HahnSeries.single 1 1)).order = _ at h
    rwa [hX, HahnSeries.order_single (one_ne_zero : (1 : k) ≠ 0)] at h
  have hlead : (E (HahnSeries.single (1 : ℤ) 1)).leadingCoeff = g.coeff 1 := by
    rw [hX, HahnSeries.leadingCoeff_eq, ho]
    exact HahnSeries.ofPowerSeries_apply_coeff g 1
  have hn (n : ℕ) : (E (HahnSeries.single (n : ℤ) 1)).leadingCoeff = g.coeff 1 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1 : LaurentSeries k) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by
        simp [HahnSeries.single_mul_single]
      rw [hs, map_mul, HahnSeries.leadingCoeff_mul, ih, hlead, pow_succ]
  have hm (m : ℤ) : (E (HahnSeries.single m 1)).leadingCoeff = g.coeff 1 ^ m := by
    cases m with
    | ofNat n =>
      change (E (HahnSeries.single (n : ℤ) 1)).leadingCoeff = g.coeff 1 ^ (n : ℤ)
      simpa only [zpow_natCast] using hn n
    | negSucc n =>
      have hp : E (HahnSeries.single (Int.negSucc n) 1) *
          E (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1) = 1 := by
        rw [← map_mul, HahnSeries.single_mul_single]
        have he : Int.negSucc n + ((n + 1 : ℕ) : ℤ) = 0 := by omega
        rw [he]
        simp
      have hl := congrArg HahnSeries.leadingCoeff hp
      rw [HahnSeries.leadingCoeff_mul, hn] at hl
      change _ * _ = (HahnSeries.single (0 : ℤ) (1 : k)).leadingCoeff at hl
      rw [HahnSeries.leadingCoeff_of_single] at hl
      have hi := eq_inv_of_mul_eq_one_left hl
      change (E (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1)).leadingCoeff =
        g.coeff 1 ^ (-((n + 1 : ℕ) : ℤ))
      rw [zpow_neg, zpow_natCast]
      exact hi
  by_cases hx : x = 0
  · simp [hx]
  have hpart : x.powerSeriesPart.constantCoeff ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      powerSeriesPart_coeff, Nat.cast_zero, add_zero, ← HahnSeries.leadingCoeff_eq]
      using (HahnSeries.leadingCoeff_ne_zero.mpr hx)
  have hc : PowerSeries.constantCoeff (x.powerSeriesPart.subst g) =
      PowerSeries.constantCoeff x.powerSeriesPart := by
    exact PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg x.powerSeriesPart
  have hp : (E (HahnSeries.ofPowerSeries ℤ k x.powerSeriesPart)).leadingCoeff =
      x.leadingCoeff := by
    rw [powerSeriesSubstEquiv_apply,
      subst_ofPowerSeries 0 IsNilpotent.zero g hg hlinear,
      leadingCoeff_ofPowerSeries_of_constantCoeff_ne_zero _ (hc ▸ hpart), hc]
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      powerSeriesPart_coeff, Nat.cast_zero, add_zero, HahnSeries.leadingCoeff_eq]
  have heq : E x = E (HahnSeries.single x.order 1) *
      E (HahnSeries.ofPowerSeries ℤ k x.powerSeriesPart) :=
    (congrArg E (single_order_mul_powerSeriesPart x)).symm.trans (map_mul E _ _)
  rw [heq, HahnSeries.leadingCoeff_mul, hm, hp]

private theorem leadingCoeff_pow (x : LaurentSeries k) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

/-- The leading coefficient of the actual Laurent derivative of a coordinate
is its nonzero linear coefficient. -/
theorem leadingCoeff_derivative_ofPowerSeries (g : PowerSeries k)
    (hlinear : IsUnit (g.coeff 1)) :
    (derivative k (HahnSeries.ofPowerSeries ℤ k g)).leadingCoeff = g.coeff 1 := by
  have hc : PowerSeries.constantCoeff (PowerSeries.derivative g) = g.coeff 1 := by
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, mul_one]
  rw [LaurentSeries.derivative_ofPowerSeries,
    leadingCoeff_ofPowerSeries_of_constantCoeff_ne_zero _ (hc ▸ hlinear.ne_zero), hc]

/-- Comparing the actual tame weighted identity forces divisibility of the
signed Laurent order. The tame multiplier is an actual coefficient unit. -/
theorem pred_dvd_order_of_weighted_coordinate (p : ℕ)
    (g : PowerSeries k) (hg : g.constantCoeff = 0) (ell : kˣ)
    (hell : g.coeff 1 = (ell : k)) (horder : orderOf ell = p - 1)
    (h : LaurentSeries k) (hne : h ≠ 0)
    (hweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg
        (hell.symm ▸ ell.isUnit) h =
      derivative k (HahnSeries.ofPowerSeries ℤ k g) ^ (p - 1) * h) :
    ((p - 1 : ℕ) : ℤ) ∣ h.order := by
  have hpow : (ell : k) ^ (p - 1) = 1 := by
    simpa only [horder, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val (pow_orderOf_eq_one ell)
  have hc := congrArg HahnSeries.leadingCoeff hweighted
  rw [leadingCoeff_powerSeriesSubstEquiv, HahnSeries.leadingCoeff_mul,
    leadingCoeff_pow, leadingCoeff_derivative_ofPowerSeries g (hell.symm ▸ ell.isUnit),
    hell, hpow, one_mul] at hc
  have hsigned : (ell : k) ^ h.order = 1 := by
    apply mul_right_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr hne)
    simpa only [one_mul] using hc
  have hu : ell ^ h.order = 1 := by
    apply Units.val_injective
    simpa using hsigned
  simpa only [horder] using
    (orderOf_dvd_iff_zpow_eq_one (x := ell) (i := h.order)).mpr hu

section PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- A principal-unit root normalizes the actual Laurent series while retaining
its original nonzero leading scalar. No coefficient-field root is chosen. -/
theorem exists_pred_pow_mul_eq_leadingCoeff (h : LaurentSeries (ZMod p))
    (hne : h ≠ 0) (hdiv : ((p - 1 : ℕ) : ℤ) ∣ h.order) :
    ∃ a : LaurentSeries (ZMod p), a ≠ 0 ∧
      a ^ (p - 1) * h = HahnSeries.C h.leadingCoeff := by
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  let β := h.leadingCoeff
  have hβ : β ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hne
  let Z : PowerSeries (ZMod p) := PowerSeries.C β⁻¹ * h.powerSeriesPart
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    change PowerSeries.constantCoeff (PowerSeries.C β⁻¹ * h.powerSeriesPart) = 1
    rw [map_mul, PowerSeries.constantCoeff_C]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff,
      Nat.cast_zero, add_zero, ← HahnSeries.leadingCoeff_eq]
    exact inv_mul_cancel₀ hβ
  have hN : IsUnit ((p - 1 : ℕ) : PadicInt p) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_p_sub_one (p := p))
  let ν : (PadicInt p)ˣ := hN.unit
  let c : PadicInt p := -((ν⁻¹ : (PadicInt p)ˣ) : PadicInt p)
  have hc : c * (p - 1 : ℕ) = -1 := by
    change -((ν⁻¹ : (PadicInt p)ˣ) : PadicInt p) * (p - 1 : ℕ) = -1
    rw [← hN.unit_spec, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let V := PowerSeries.principalUnitPow Z hZ c
  have hV : V ^ (p - 1) * Z = 1 := by
    rw [← PowerSeries.principalUnitPow_mul_natCast, hc]
    simpa only [PowerSeries.principalUnitPow_one] using
      PowerSeries.principalUnitPow_neg_mul Z hZ 1
  have heV : e V ^ (p - 1) * e Z = 1 := by
    simpa only [map_mul, map_pow, map_one] using congrArg e hV
  obtain ⟨j, hj⟩ := hdiv
  let a : LaurentSeries (ZMod p) := HahnSeries.single (-j) 1 * e V
  have hdecomp : HahnSeries.single h.order β * e Z = h := by
    change HahnSeries.single h.order β * e (PowerSeries.C β⁻¹ * h.powerSeriesPart) = h
    rw [map_mul, HahnSeries.ofPowerSeries_C, ← mul_assoc]
    change HahnSeries.single h.order β * HahnSeries.single (0 : ℤ) β⁻¹ *
      e h.powerSeriesPart = h
    rw [HahnSeries.single_mul_single, add_zero, mul_inv_cancel₀ hβ]
    exact single_order_mul_powerSeriesPart h
  have heq : a ^ (p - 1) * h = HahnSeries.C β := by
    calc
      a ^ (p - 1) * h = a ^ (p - 1) *
          (HahnSeries.single h.order β * e Z) :=
            congrArg (fun x => a ^ (p - 1) * x) hdecomp.symm
      _ = (HahnSeries.single (-j) (1 : ZMod p)) ^ (p - 1) *
          HahnSeries.single h.order β * (e V ^ (p - 1) * e Z) := by
            rw [show a = HahnSeries.single (-j) 1 * e V from rfl, mul_pow]
            ring
      _ = (HahnSeries.single (-j) (1 : ZMod p)) ^ (p - 1) *
          HahnSeries.single h.order β := by
            rw [heV, mul_one]
      _ = HahnSeries.C β := by
        rw [HahnSeries.single_pow, HahnSeries.single_mul_single, one_pow, one_mul]
        have he : (p - 1) • (-j) + h.order = 0 := by rw [hj, nsmul_eq_mul]; ring
        rw [he]
        rfl
  refine ⟨a, ?_, heq⟩
  intro ha
  have hp := (Fact.out : p.Prime).two_le
  rw [ha, zero_pow (by omega : p - 1 ≠ 0), zero_mul] at heq
  apply hβ
  have hz : (HahnSeries.C β : LaurentSeries (ZMod p)) = HahnSeries.C 0 := by
    simpa only [map_zero] using heq.symm
  exact HahnSeries.C_injective hz

/-- An actual Laurent principal unit has no nontrivial `(p-1)`st torsion.
The power-series representative is constructed from its original coefficients. -/
theorem eq_one_of_pred_pow_eq_one (r : LaurentSeries (ZMod p))
    (ho : r.order = 0) (hl : r.leadingCoeff = 1) (hp : r ^ (p - 1) = 1) :
    r = 1 := by
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  let R := PowerSeries.mk (fun n : ℕ ↦ r.coeff n)
  have hr0 : r ∈ orderAddSubgroup 0 := by
    simpa only [ho] using mem_orderAddSubgroup_order r
  have hR : e R = r := ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero r hr0
  have hc : PowerSeries.constantCoeff R = 1 := by
    simpa only [R, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, Nat.cast_zero, HahnSeries.leadingCoeff_eq, ho] using hl
  have hpow : R ^ (p - 1) = 1 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change e (R ^ (p - 1)) = e 1
    rw [map_pow, hR, map_one]
    exact hp
  have hnot : ¬ p ∣ p - 1 := by
    have hprime := (Fact.out : p.Prime).two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hord := PowerSeries.order_pow_sub_one_of_not_dvd R hc (p - 1) hnot
  rw [hpow, sub_self, PowerSeries.order_zero] at hord
  have hone : R = 1 := sub_eq_zero.mp (PowerSeries.order_eq_top.mp hord.symm)
  rw [← hR, hone, map_one]

private theorem invariant_of_pred_pow_normalization
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (h a : LaurentSeries (ZMod p)) (ha : a ≠ 0)
    (hweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
        (hlinear ▸ isUnit_one) h =
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) ^ (p - 1) * h)
    (β : ZMod p) (hβ : β ≠ 0)
    (hnorm : a ^ (p - 1) * h = HahnSeries.C β) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero f hf (hlinear ▸ isUnit_one) a *
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) = a := by
  let E := powerSeriesSubstEquiv (0 : ZMod p) IsNilpotent.zero f hf (hlinear ▸ isUnit_one)
  let D := derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f)
  have hEa : E a ≠ 0 := by
    intro hz
    apply ha
    apply E.injective
    simpa only [map_zero] using hz
  have hD : D ≠ 0 :=
    (LaurentSeries.isUnit_derivative_ofPowerSeries f (hlinear ▸ isUnit_one)).ne_zero
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hnorm
    have hz' : (HahnSeries.C β : LaurentSeries (ZMod p)) = HahnSeries.C 0 := by
      simpa only [map_zero] using hnorm.symm
    exact hβ (HahnSeries.C_injective hz')
  let r := E a * D / a
  have hr : r ≠ 0 := div_ne_zero (mul_ne_zero hEa hD) ha
  have hprod : r * a = E a * D := div_mul_cancel₀ _ ha
  have hC : E (HahnSeries.C β) = HahnSeries.C β := by
    simpa only [LaurentSeries.algebraMap_apply] using E.commutes β
  have he := congrArg E hnorm
  rw [map_mul, map_pow, hC] at he
  change E a ^ (p - 1) * (E h) = HahnSeries.C β at he
  rw [hweighted] at he
  have hpowmul : r ^ (p - 1) * (a ^ (p - 1) * h) = a ^ (p - 1) * h := by
    calc
      _ = (r * a) ^ (p - 1) * h := by rw [mul_pow]; ring
      _ = (E a * D) ^ (p - 1) * h := by rw [hprod]
      _ = E a ^ (p - 1) * (D ^ (p - 1) * h) := by rw [mul_pow]; ring
      _ = HahnSeries.C β := he
      _ = a ^ (p - 1) * h := hnorm.symm
  have hpow : r ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ ha) hh)
    simpa only [one_mul] using hpowmul
  have hEorder : (E a).order = a.order := order_powerSeriesSubstEquiv f hf _ a
  have hDorder : D.order = 0 := order_derivative_ofPowerSeries f (hlinear ▸ isUnit_one)
  have hrorder : r.order = 0 := by
    have ho := congrArg HahnSeries.order hprod
    rw [HahnSeries.order_mul hr ha, HahnSeries.order_mul hEa hD, hEorder, hDorder,
      add_zero] at ho
    omega
  have hElead : (E a).leadingCoeff = a.leadingCoeff := by
    rw [leadingCoeff_powerSeriesSubstEquiv, hlinear, one_zpow, one_mul]
  have hDlead : D.leadingCoeff = 1 := by
    rw [leadingCoeff_derivative_ofPowerSeries f (hlinear ▸ isUnit_one), hlinear]
  have hrlead : r.leadingCoeff = 1 := by
    have hc := congrArg HahnSeries.leadingCoeff hprod
    rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, hElead, hDlead,
      mul_one] at hc
    apply mul_right_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr ha)
    simpa only [one_mul] using hc
  have hrone := eq_one_of_pred_pow_eq_one p r hrorder hrlead hpow
  simpa only [hrone, one_mul] using hprod.symm

/-- Two actual weighted coordinate identities for a nonzero exact Laurent
series produce an actual nonzero exact invariant differential. Only the tame
linear coefficient has prescribed order; no order assumption on either
substitution automorphism is needed. -/
theorem exists_exact_invariant_of_weighted_identities
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (g : PowerSeries (ZMod p)) (hg : g.constantCoeff = 0)
    (ell : (ZMod p)ˣ) (hell : g.coeff 1 = (ell : ZMod p))
    (horder : orderOf ell = p - 1)
    (h A : LaurentSeries (ZMod p)) (hne : h ≠ 0) (hA : derivative (ZMod p) A = h)
    (hfweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
        (hlinear ▸ isUnit_one) h =
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) ^ (p - 1) * h)
    (hgweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg
        (hell.symm ▸ ell.isUnit) h =
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) g) ^ (p - 1) * h) :
    ∃ a B : LaurentSeries (ZMod p), a ≠ 0 ∧ derivative (ZMod p) B = a ∧
      powerSeriesSubstEquiv 0 IsNilpotent.zero f hf (hlinear ▸ isUnit_one) a *
        derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) = a := by
  have hdiv := pred_dvd_order_of_weighted_coordinate p g hg ell hell horder h hne hgweighted
  obtain ⟨a, ha, hnorm⟩ := exists_pred_pow_mul_eq_leadingCoeff p h hne hdiv
  let β := h.leadingCoeff
  have hβ : β ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hne
  have hinvariant := invariant_of_pred_pow_normalization p f hf hlinear h a ha
    hfweighted β hβ hnorm
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hpowa : a ^ p = a ^ (p - 1) * a := by
    simpa only [hpred] using pow_succ a (p - 1)
  have haph : a ^ p * h = HahnSeries.C β * a := by
    calc
      a ^ p * h = a * (a ^ (p - 1) * h) := by rw [hpowa]; ring
      _ = a * HahnSeries.C β := by rw [hnorm]
      _ = HahnSeries.C β * a := mul_comm _ _
  have hDpow : derivative (ZMod p) (a ^ p) = 0 := by
    let : CharP (LaurentSeries (ZMod p)) p :=
      ((algebraMap (ZMod p) (LaurentSeries (ZMod p))).charP_iff_charP p).mp inferInstance
    simpa only [hpred, CharP.cast_eq_zero, zero_mul] using derivative_pow_succ a (p - 1)
  let B : LaurentSeries (ZMod p) := HahnSeries.C β⁻¹ * a ^ p * A
  refine ⟨a, B, ha, ?_, hinvariant⟩
  change derivative (ZMod p) (HahnSeries.C β⁻¹ * a ^ p * A) = a
  rw [derivative_mul, derivative_mul, derivative_C, hDpow, zero_mul, mul_zero,
    zero_add, zero_mul, zero_add, hA]
  calc
    HahnSeries.C β⁻¹ * a ^ p * h = HahnSeries.C β⁻¹ * (a ^ p * h) := mul_assoc _ _ _
    _ = HahnSeries.C β⁻¹ * (HahnSeries.C β * a) := by rw [haph]
    _ = a := by
      change HahnSeries.single (0 : ℤ) β⁻¹ * (HahnSeries.single (0 : ℤ) β * a) = a
      rw [← mul_assoc, HahnSeries.single_mul_single, zero_add, inv_mul_cancel₀ hβ]
      simp

end PrimeField

end LaurentSeries
