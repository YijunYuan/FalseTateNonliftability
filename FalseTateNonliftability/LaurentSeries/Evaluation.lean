/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.PowerSeriesEval
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Laurent evaluation by localization

A unit plus a nilpotent perturbation is a unit. The actual power-series
evaluation therefore extends along the canonical localization
`R[[X]] → R((X))` to an algebra homomorphism on the same Laurent carrier.
Its restriction to all power series determines it uniquely; no topological
or uniqueness-from-the-variable assertion is needed.

This is blueprint lemma `nl:laurent-evaluation`.
-/

@[expose] public section

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- Adding a nilpotent constant multiple to a unit preserves invertibility. -/
theorem isUnit_nilpotent_perturbation (δ : R) (U Y : LaurentSeries R)
    (hδ : IsNilpotent δ) (hUunit : IsUnit U) : IsUnit (U + HahnSeries.C δ * Y) := by
  have hC : IsNilpotent (HahnSeries.C δ : LaurentSeries R) := hδ.map HahnSeries.C
  have hCY := (Commute.all (HahnSeries.C δ) Y).isNilpotent_mul_right hC
  exact hCY.isUnit_add_left_of_commute hUunit (Commute.all _ _)

-- The localization API uses the scalar actions supplied by these algebras.
-- This is the canonical composition tower; its algebra maps agree definitionally.
local instance : @IsScalarTower R (PowerSeries R) (LaurentSeries R)
    (inferInstance : Algebra R (PowerSeries R)).toSMul
    (inferInstance : Algebra (PowerSeries R) (LaurentSeries R)).toSMul
    (inferInstance : Algebra R (LaurentSeries R)).toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

local notation "G" => U + HahnSeries.C δ * Y
local notation "powerEval" => nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY
local notation "gUnit" => IsUnit.unit
  (isUnit_nilpotent_perturbation δ U Y (Exists.intro r hδ) hUunit)

/-- The canonical localization extension of the actual summable power-series
evaluation at a unit with a nilpotent perturbation. -/
def nilpotentLaurentEval : LaurentSeries R →ₐ[R] LaurentSeries R :=
  IsLocalization.Away.liftAlgHom (S := LaurentSeries R) (f := powerEval) PowerSeries.X <| by
    rw [nilpotentPowerSeriesEval_X]
    exact isUnit_nilpotent_perturbation δ U Y ⟨r, hδ⟩ hUunit

local notation "laurentEval" => nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit

/-- Restriction to every power series is the previously constructed evaluation. -/
@[simp]
theorem nilpotentLaurentEval_ofPowerSeries (f : PowerSeries R) :
    laurentEval (HahnSeries.ofPowerSeries ℤ R f) = powerEval f := by
  simp only [nilpotentLaurentEval, IsLocalization.Away.liftAlgHom_apply]
  exact IsLocalization.Away.lift_eq _ _ f

@[simp]
theorem nilpotentLaurentEval_C (b : R) :
    laurentEval (HahnSeries.C b) = HahnSeries.C b := by
  simpa only [HahnSeries.ofPowerSeries_C, nilpotentPowerSeriesEval_C] using
    nilpotentLaurentEval_ofPowerSeries δ U Y r hr hδ a c ha hc hU hY hUunit (PowerSeries.C b)

/-- The Laurent variable is sent to the actual perturbed unit. -/
@[simp]
theorem nilpotentLaurentEval_X : laurentEval (HahnSeries.single (1 : ℤ) (1 : R)) = G := by
  simpa only [HahnSeries.ofPowerSeries_X, nilpotentPowerSeriesEval_X] using
    nilpotentLaurentEval_ofPowerSeries δ U Y r hr hδ a c ha hc hU hY hUunit PowerSeries.X

/-- The inverse Laurent variable maps to the inverse in the actual unit group.
This formula does not require an inverse operation on the coefficient ring. -/
@[simp]
theorem nilpotentLaurentEval_X_inv :
    laurentEval (HahnSeries.single (-1 : ℤ) (1 : R)) = (↑(gUnit⁻¹) : LaurentSeries R) := by
  apply Units.eq_inv_of_mul_eq_one_left
  rw [IsUnit.unit_spec, ← nilpotentLaurentEval_X δ U Y r hr hδ a c ha hc hU hY hUunit,
    ← map_mul]
  simp

/-- Integer powers of the Laurent variable evaluate to powers in the unit
group, so negative exponents work over arbitrary commutative coefficient rings. -/
theorem nilpotentLaurentEval_single_one (n : ℤ) :
    laurentEval (HahnSeries.single n (1 : R)) = (↑(gUnit ^ n) : LaurentSeries R) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hs : (HahnSeries.single ((n : ℤ) + 1) (1 : R) : LaurentSeries R) =
        HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by simp
    rw [hs, map_mul, ih, nilpotentLaurentEval_X, zpow_add, zpow_one,
      Units.val_mul, IsUnit.unit_spec]
  | pred n ih =>
    have hs : (HahnSeries.single (-(n : ℤ) - 1) (1 : R) : LaurentSeries R) =
        HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-1 : ℤ) 1 := by
      simp [sub_eq_add_neg]
    rw [hs, map_mul, ih, nilpotentLaurentEval_X_inv, zpow_sub, zpow_one, Units.val_mul]

/-- Evaluation of every integer Laurent monomial. -/
theorem nilpotentLaurentEval_single (n : ℤ) (b : R) :
    laurentEval (HahnSeries.single n b) = HahnSeries.C b * (↑(gUnit ^ n) : LaurentSeries R) := by
  have hs : (HahnSeries.single n b : LaurentSeries R) =
      HahnSeries.C b * HahnSeries.single n 1 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hs, map_mul, nilpotentLaurentEval_C, nilpotentLaurentEval_single_one]

/-- In particular all negative monomials are evaluated by ordinary natural
powers of the inverse unit, without assuming a field of coefficients. -/
theorem nilpotentLaurentEval_single_neg (n : ℕ) (b : R) :
    laurentEval (HahnSeries.single (-(n : ℤ)) b) =
      HahnSeries.C b * (↑((gUnit⁻¹) ^ n) : LaurentSeries R) := by
  rw [nilpotentLaurentEval_single, zpow_neg, zpow_natCast, inv_pow]

/-- Evaluation of the canonical decomposition into an integer monomial
and the shifted power-series part. It includes the zero Laurent series. -/
theorem nilpotentLaurentEval_eq_powerSeriesPart (f : LaurentSeries R) :
    laurentEval f = (↑(gUnit ^ f.order) : LaurentSeries R) * powerEval f.powerSeriesPart := by
  conv_lhs => rw [← f.single_order_mul_powerSeriesPart]
  rw [map_mul, nilpotentLaurentEval_single_one, nilpotentLaurentEval_ofPowerSeries]

/-- Agreement on all power series uniquely determines the localization
extension. Agreement on the variable alone is not asserted. -/
theorem nilpotentLaurentEval_unique (F : LaurentSeries R →ₐ[R] LaurentSeries R)
    (hF : ∀ f : PowerSeries R, F (HahnSeries.ofPowerSeries ℤ R f) = powerEval f) :
    F = laurentEval := by
  apply IsLocalization.algHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries R))
  apply AlgHom.ext
  intro f
  change F (HahnSeries.ofPowerSeries ℤ R f) = laurentEval (HahnSeries.ofPowerSeries ℤ R f)
  rw [hF, nilpotentLaurentEval_ofPowerSeries]

end

end LaurentSeries
