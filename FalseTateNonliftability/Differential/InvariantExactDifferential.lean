/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition
public import FalseTateNonliftability.PowerSeries.PrincipalUnits

/-!
# Invariant exact differentials from two weighted identities

Let `κ` be a field of characteristic `p`. A power series `f ∈ T κ⟦T⟧` with invertible linear
coefficient defines the automorphism `σ_f : x ↦ x(f)` of `κ((T))`, which acts on differentials by
`σ_f(a dT) = a(f) f' dT`. Let `f ∈ T + T ^ 2 κ⟦T⟧`, let `g ∈ T κ⟦T⟧` have linear coefficient
`λ` of multiplicative order `p - 1`, and let `h = A' ≠ 0` satisfy the weighted identities
`h(f) = (f') ^ (p - 1) h` and `h(g) = (g') ^ (p - 1) h`. The leading coefficients of the second
identity give `λ ^ v_T(h) = 1`, hence `p - 1 ∣ v_T(h)`, and `a ^ (p - 1) h = b` for some
`a ∈ κ((T))ˣ`, where `b` is the leading coefficient of `h`. The differential `ω = a dT` is fixed by
`σ_f`, and it is exact: `ω = d(b⁻¹ a ^ p A)`.

## Main results

* `LaurentSeries.leadingCoeff_substEquiv`: the leading coefficient of `x(g)` is `λ ^ v_T(x)`
  times that of `x`.
* `LaurentSeries.exists_exact_invariant_of_weighted_identities`: the nonzero exact differential
  fixed by `σ_f` (Yuan, Lemma 4.1).

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.1.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

variable {κ : Type*} [Field κ]

/-- The leading coefficient `κ((T)) → κ` as a homomorphism of monoids with zero. -/
private def leadingCoeffHom : LaurentSeries κ →*₀ κ where
  toFun := HahnSeries.leadingCoeff
  map_zero' := HahnSeries.leadingCoeff_zero
  map_one' := HahnSeries.leadingCoeff_one
  map_mul' x y := HahnSeries.leadingCoeff_mul x y

private theorem leadingCoeffHom_apply (x : LaurentSeries κ) :
    leadingCoeffHom x = x.leadingCoeff :=
  rfl

private theorem leadingCoeff_pow (x : LaurentSeries κ) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  rw [← leadingCoeffHom_apply, map_pow, leadingCoeffHom_apply]

private theorem leadingCoeff_zpow (x : LaurentSeries κ) (m : ℤ) :
    (x ^ m).leadingCoeff = x.leadingCoeff ^ m := by
  rw [← leadingCoeffHom_apply, map_zpow₀, leadingCoeffHom_apply]

private theorem leadingCoeff_ofPowerSeries {P : PowerSeries κ} (hP : P.constantCoeff ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ κ P).leadingCoeff = P.constantCoeff := by
  have hunit : IsUnit P := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hP)
  have hne : HahnSeries.ofPowerSeries ℤ κ P ≠ 0 :=
    (hunit.map (HahnSeries.ofPowerSeries ℤ κ)).ne_zero
  have ho : (HahnSeries.ofPowerSeries ℤ κ P).order = 0 := by
    have htop : (HahnSeries.ofPowerSeries ℤ κ P).orderTop = 0 := by
      rw [HahnSeries.orderTop_ofPowerSeries, PowerSeries.order_zero_of_isUnit hunit]
      rfl
    exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hne).trans htop
  rw [HahnSeries.leadingCoeff_eq, ho]
  simpa using HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) P 0

private theorem constantCoeff_powerSeriesPart (x : LaurentSeries κ) :
    x.powerSeriesPart.constantCoeff = x.leadingCoeff := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
    add_zero, HahnSeries.leadingCoeff_eq]

/-- Let `g ∈ T κ⟦T⟧` have invertible linear coefficient `λ`. The leading coefficient of `x(g)` is
`λ ^ v_T(x)` times the leading coefficient of `x`. -/
theorem leadingCoeff_substEquiv {g : PowerSeries κ} (hg : g.constantCoeff = 0)
    (hlinear : IsUnit (g.coeff 1)) (x : LaurentSeries κ) :
    (substEquiv g x).leadingCoeff = g.coeff 1 ^ x.order * x.leadingCoeff := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨w, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  have hw : (PowerSeries.X * w).coeff 1 = w.constantCoeff := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hX : (HahnSeries.ofPowerSeries ℤ κ (PowerSeries.X * w)).leadingCoeff =
      w.constantCoeff := by
    rw [map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.leadingCoeff_mul,
      HahnSeries.leadingCoeff_of_single, one_mul,
      leadingCoeff_ofPowerSeries (hw ▸ hlinear.ne_zero)]
  have hP : PowerSeries.constantCoeff (x.powerSeriesPart.subst (PowerSeries.X * w)) =
      x.leadingCoeff := by
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero' hg, constantCoeff_powerSeriesPart]
  conv_lhs => rw [← single_order_mul_powerSeriesPart x, RatFunc.single_zpow]
  rw [map_mul, map_zpow₀, substEquiv_X hg hlinear, substEquiv_ofPowerSeries hg hlinear,
    HahnSeries.leadingCoeff_mul, leadingCoeff_zpow, hX, hw,
    leadingCoeff_ofPowerSeries (hP ▸ HahnSeries.leadingCoeff_ne_zero.mpr hx), hP]

/-- If the linear coefficient `λ` of `g ∈ κ⟦T⟧` is invertible, then the leading coefficient of
`g'` is `λ`. -/
theorem leadingCoeff_derivative_ofPowerSeries {g : PowerSeries κ}
    (hlinear : IsUnit (g.coeff 1)) :
    (derivative κ (HahnSeries.ofPowerSeries ℤ κ g)).leadingCoeff = g.coeff 1 := by
  have hc : (PowerSeries.derivative g).constantCoeff = g.coeff 1 := by
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
      zero_add, Nat.cast_zero, mul_one]
  rw [derivative_ofPowerSeries, leadingCoeff_ofPowerSeries (hc ▸ hlinear.ne_zero), hc]

/-- If `h ≠ 0` satisfies `h(g) = (g') ^ n h` and the linear coefficient `λ` of `g` has
multiplicative order `n`, then `n ∣ v_T(h)`. -/
private theorem dvd_order_of_substEquiv_eq {g : PowerSeries κ} (hg : g.constantCoeff = 0)
    {n : ℕ} (hn : 0 < n) (hg1 : orderOf (g.coeff 1) = n) {h : LaurentSeries κ} (hne : h ≠ 0)
    (hgh : substEquiv g h = derivative κ (HahnSeries.ofPowerSeries ℤ κ g) ^ n * h) :
    (n : ℤ) ∣ h.order := by
  have hlinear : IsUnit (g.coeff 1) := (orderOf_pos_iff.mp (hg1 ▸ hn)).isUnit
  have hc := congrArg HahnSeries.leadingCoeff hgh
  rw [leadingCoeff_substEquiv hg hlinear, HahnSeries.leadingCoeff_mul, leadingCoeff_pow,
    leadingCoeff_derivative_ofPowerSeries hlinear, ← hg1, pow_orderOf_eq_one, one_mul] at hc
  have hz : g.coeff 1 ^ h.order = 1 :=
    mul_right_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr hne) (hc.trans (one_mul _).symm)
  rw [← hg1, ← hlinear.unit_spec, orderOf_units]
  exact orderOf_dvd_iff_zpow_eq_one.mpr
    (Units.val_injective (by rwa [Units.val_zpow_eq_zpow_val, Units.val_one]))

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP κ p]

/-- If `p - 1 ∣ v_T(h)` for a nonzero `h`, then `a ^ (p - 1) h` equals the leading coefficient of
`h` for some nonzero `a`. -/
private theorem exists_pow_mul_eq_C_leadingCoeff {h : LaurentSeries κ} (hne : h ≠ 0)
    (hdiv : ((p - 1 : ℕ) : ℤ) ∣ h.order) :
    ∃ a : LaurentSeries κ, a ≠ 0 ∧ a ^ (p - 1) * h = HahnSeries.C h.leadingCoeff := by
  have hβ : h.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hne
  set Z : PowerSeries κ := PowerSeries.C h.leadingCoeff⁻¹ * h.powerSeriesPart with hZdef
  have hZ : Z.constantCoeff = 1 := by
    rw [hZdef, map_mul, PowerSeries.constantCoeff_C, constantCoeff_powerSeriesPart,
      inv_mul_cancel₀ hβ]
  obtain ⟨ν, hν⟩ : IsUnit ((p - 1 : ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_p_sub_one (p := p))
  set c : ℤ_[p] := -((ν⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have hc : c * ((p - 1 : ℕ) : ℤ_[p]) = -1 := by
    rw [hcdef, ← hν, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hV : PowerSeries.principalUnitPow Z c ^ (p - 1) * Z = 1 := by
    rw [← PowerSeries.principalUnitPow_mul_natCast hZ, hc]
    simpa only [PowerSeries.principalUnitPow_one hZ] using
      PowerSeries.principalUnitPow_neg_mul hZ (1 : ℤ_[p])
  obtain ⟨j, hj⟩ := hdiv
  have hh : h = HahnSeries.single h.order h.leadingCoeff * HahnSeries.ofPowerSeries ℤ κ Z := by
    rw [hZdef, map_mul, HahnSeries.ofPowerSeries_C, ← mul_assoc, HahnSeries.C_apply,
      HahnSeries.single_mul_single, add_zero, mul_inv_cancel₀ hβ,
      single_order_mul_powerSeriesPart]
  refine ⟨HahnSeries.single (-j) 1 *
    HahnSeries.ofPowerSeries ℤ κ (PowerSeries.principalUnitPow Z c), ?_, ?_⟩
  · refine mul_ne_zero (by simp) fun h0 ↦ ?_
    have h1 := congrArg (HahnSeries.ofPowerSeries ℤ κ) hV
    rw [map_mul, map_pow, h0, zero_pow (by have := (Fact.out : p.Prime).two_le; omega),
      zero_mul, map_one] at h1
    exact zero_ne_one h1
  · have h1 := congrArg (HahnSeries.ofPowerSeries ℤ κ) hV
    rw [map_mul, map_pow, map_one] at h1
    have he : (p - 1) • (-j) + h.order = 0 := by
      rw [hj, nsmul_eq_mul]
      ring
    calc
      _ = HahnSeries.single (-j) (1 : κ) ^ (p - 1) * HahnSeries.single h.order h.leadingCoeff *
          (HahnSeries.ofPowerSeries ℤ κ (PowerSeries.principalUnitPow Z c) ^ (p - 1) *
            HahnSeries.ofPowerSeries ℤ κ Z) := by
        conv_lhs => rw [hh]
        ring
      _ = HahnSeries.C h.leadingCoeff := by
        rw [h1, mul_one, HahnSeries.single_pow, HahnSeries.single_mul_single, one_pow, one_mul,
          he, HahnSeries.C_apply]

/-- In characteristic `p`, the only `r = 1 + O(T)` in `κ((T))` with `r ^ (p - 1) = 1` is `1`. -/
private theorem eq_one_of_pow_sub_one_eq_one {r : LaurentSeries κ} (ho : r.order = 0)
    (hl : r.leadingCoeff = 1) (hr : r ^ (p - 1) = 1) : r = 1 := by
  have hR : HahnSeries.ofPowerSeries ℤ κ r.powerSeriesPart = r := by
    simpa only [ho, HahnSeries.single_zero_one, one_mul] using single_order_mul_powerSeriesPart r
  have hc : r.powerSeriesPart.constantCoeff = 1 := by rw [constantCoeff_powerSeriesPart, hl]
  have hpow : r.powerSeriesPart ^ (p - 1) = 1 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_pow, hR, map_one, hr]
  have hnot : ¬ p ∣ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hord := PowerSeries.order_pow_sub_one_of_not_dvd r.powerSeriesPart hc (p - 1) hnot
  rw [hpow, sub_self, PowerSeries.order_zero, eq_comm, PowerSeries.order_eq_top,
    sub_eq_zero] at hord
  rw [← hR, hord, map_one]

/-- If `h(f) = (f') ^ (p - 1) h` for `f ∈ T + T ^ 2 κ⟦T⟧` and `a ^ (p - 1) h` is a nonzero
constant, then `a(f) f' = a`. -/
private theorem substEquiv_mul_derivative_eq {f : PowerSeries κ} (hf : f.constantCoeff = 0)
    (hf1 : f.coeff 1 = 1) {h a : LaurentSeries κ} (ha : a ≠ 0)
    (hfh : substEquiv f h = derivative κ (HahnSeries.ofPowerSeries ℤ κ f) ^ (p - 1) * h)
    {β : κ} (hβ : β ≠ 0) (hnorm : a ^ (p - 1) * h = HahnSeries.C β) :
    substEquiv f a * derivative κ (HahnSeries.ofPowerSeries ℤ κ f) = a := by
  have hf' : IsUnit (f.coeff 1) := hf1 ▸ isUnit_one
  set D := derivative κ (HahnSeries.ofPowerSeries ℤ κ f) with hDdef
  have hEa : substEquiv f a ≠ 0 := (map_ne_zero_iff _ (substEquiv f).injective).mpr ha
  have hD : D ≠ 0 := (isUnit_derivative_ofPowerSeries f hf').ne_zero
  have hh : h ≠ 0 := by
    rintro rfl
    rw [mul_zero, eq_comm, map_eq_zero_iff _ HahnSeries.C_injective] at hnorm
    exact hβ hnorm
  set r := substEquiv f a * D / a
  have hprod : r * a = substEquiv f a * D := div_mul_cancel₀ _ ha
  have hC : substEquiv f (HahnSeries.C β) = HahnSeries.C β := by
    simpa only [algebraMap_apply] using (substEquiv f).commutes β
  have he := congrArg (substEquiv f) hnorm
  rw [map_mul, map_pow, hC, hfh] at he
  have hpow : r ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (p - 1) ha) hh)
    calc
      r ^ (p - 1) * (a ^ (p - 1) * h) = (r * a) ^ (p - 1) * h := by ring
      _ = substEquiv f a ^ (p - 1) * (D ^ (p - 1) * h) := by rw [hprod]; ring
      _ = 1 * (a ^ (p - 1) * h) := by rw [he, hnorm, one_mul]
  have hr : r ≠ 0 := div_ne_zero (mul_ne_zero hEa hD) ha
  have hrorder : r.order = 0 := by
    have ho := congrArg HahnSeries.order hprod
    rw [HahnSeries.order_mul hr ha, HahnSeries.order_mul hEa hD, order_substEquiv hf hf',
      order_derivative_ofPowerSeries hf', add_zero] at ho
    omega
  have hrlead : r.leadingCoeff = 1 := by
    have hc := congrArg HahnSeries.leadingCoeff hprod
    rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, leadingCoeff_substEquiv hf hf',
      hDdef, leadingCoeff_derivative_ofPowerSeries hf', hf1, one_zpow, one_mul, mul_one] at hc
    exact mul_right_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr ha) (hc.trans (one_mul _).symm)
  rw [← hprod, eq_one_of_pow_sub_one_eq_one p hrorder hrlead hpow, one_mul]

/-- **Construction of an invariant exact differential** (Yuan, Lemma 4.1). Let `κ` be a field of
characteristic `p`, let `f ∈ T + T ^ 2 κ⟦T⟧`, and let `g ∈ T κ⟦T⟧` have linear coefficient of
multiplicative order `p - 1`. If a nonzero exact Laurent series `h = A'` satisfies
`h(f) = (f') ^ (p - 1) h` and `h(g) = (g') ^ (p - 1) h`, then there is a nonzero exact
differential `ω = a dT = dB` fixed by `σ_f`, that is, `a(f) f' = a`. -/
theorem exists_exact_invariant_of_weighted_identities {f g : PowerSeries κ}
    (hf : f.constantCoeff = 0) (hf1 : f.coeff 1 = 1) (hg : g.constantCoeff = 0)
    (hg1 : orderOf (g.coeff 1) = p - 1) {h A : LaurentSeries κ} (hne : h ≠ 0)
    (hA : derivative κ A = h)
    (hfh : substEquiv f h = derivative κ (HahnSeries.ofPowerSeries ℤ κ f) ^ (p - 1) * h)
    (hgh : substEquiv g h = derivative κ (HahnSeries.ofPowerSeries ℤ κ g) ^ (p - 1) * h) :
    ∃ a B : LaurentSeries κ, a ≠ 0 ∧ derivative κ B = a ∧
      substEquiv f a * derivative κ (HahnSeries.ofPowerSeries ℤ κ f) = a := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨a, ha, hnorm⟩ := exists_pow_mul_eq_C_leadingCoeff p hne
    (dvd_order_of_substEquiv_eq hg (by omega) hg1 hne hgh)
  have hβ : h.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hne
  have hpred : p - 1 + 1 = p := by omega
  have : CharP (LaurentSeries κ) p :=
    ((algebraMap κ (LaurentSeries κ)).charP_iff_charP p).mp inferInstance
  have hDpow : derivative κ (a ^ p) = 0 := by
    simpa only [hpred, CharP.cast_eq_zero, zero_mul] using derivative_pow_succ a (p - 1)
  refine ⟨a, HahnSeries.C h.leadingCoeff⁻¹ * a ^ p * A, ha, ?_,
    substEquiv_mul_derivative_eq p hf hf1 ha hfh hβ hnorm⟩
  rw [derivative_mul, derivative_mul, derivative_C, hDpow, zero_mul, mul_zero, zero_add,
    zero_mul, zero_add, hA]
  calc
    HahnSeries.C h.leadingCoeff⁻¹ * a ^ p * h =
        HahnSeries.C h.leadingCoeff⁻¹ * a * (a ^ (p - 1) * h) := by
      rw [show a ^ p = a * a ^ (p - 1) by rw [← pow_succ', hpred]]
      ring
    _ = a := by
      rw [hnorm, mul_comm _ a, mul_assoc, ← map_mul, inv_mul_cancel₀ hβ, map_one, mul_one]

end CharP

end LaurentSeries
