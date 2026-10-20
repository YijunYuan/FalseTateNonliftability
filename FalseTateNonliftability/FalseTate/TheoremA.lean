/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Liftability
public import FalseTateNonliftability.FieldOfNorms.Liftability
public import FalseTateExtension.Padic.NormFieldAction

/-!
# Non-liftability of the original false Tate action

The actual prime-field coordinates are transported through the residue
isomorphism of the original totally ramified coefficient extension.
-/

@[expose] public section

noncomputable section

open Filter FontaineWintenberger FalseTateExtension WithZero LaurentSeries
open scoped Topology

namespace FalseTateNonliftability

attribute [local instance] FalseTateExtension.normFieldCoordinatesResidueCharP
  FalseTateExtension.normFieldCoordinatesResiduePerfect
  FalseTateExtension.normFieldCoordinatesIntegralClosureValuationRing
  CoefficientRing.finiteObstructionZeroSpanIsMaximal

private theorem laurent_displacement_order_of_powerSeries_order
    {k : Type*} [Field k] (f : PowerSeries k) (n : ℕ)
    (h : (f - PowerSeries.X).order = (n : ℕ∞)) :
    (HahnSeries.ofPowerSeries ℤ k f - HahnSeries.single (1 : ℤ) 1).order = (n : ℤ) := by
  have hne : f - PowerSeries.X ≠ 0 := by
    intro hz
    simp only [hz, PowerSeries.order_zero, ENat.top_ne_natCast] at h
  have hm : HahnSeries.ofPowerSeries ℤ k (f - PowerSeries.X) ≠ 0 := by
    intro hz
    apply hne
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using hz
  have ho : (HahnSeries.ofPowerSeries ℤ k (f - PowerSeries.X)).order = (n : ℤ) := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hm, HahnSeries.orderTop_ofPowerSeries, h]
    rfl
  simpa only [map_sub, HahnSeries.ofPowerSeries_X] using ho

variable (p : ℕ) [Fact p.Prime]
variable {π : (NormedField.valuation (K := Padic p)).valuationSubring}
variable (hp₂ : p ≠ 2) (hπ : Irreducible π)
variable (F : Type*) [Field F] [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "FT" => falseTateExtension p (π : Padic p)
local notation "O_F" => spectralIntegerRing (Padic p) F
local notation "O_0" => Valuation.valuationSubring (NormedField.valuation (K := Padic p))
local notation "κF" => IsLocalRing.ResidueField O_F

variable (htotal : (IsLocalRing.maximalIdeal (spectralIntegerRing (Padic p) F)).ramificationIdx
  (Valuation.valuationSubring (NormedField.valuation (K := Padic p))) = Module.finrank (Padic p) F)
variable (u : NormLimit (Padic p) (falseTateExtension p (π : Padic p)))
variable (hu : normLimitValuation (Padic p) (falseTateExtension p (π : Padic p))
  (isAPF_falseTateExtension p hπ) u = exp (-1 : ℤ))

/-- The original false Tate coordinate with coefficients in the actual residue
field of the totally ramified coefficient extension. -/
def falseTateCoefficientCoordinate (g : FT ≃ₐ[Padic p] FT) : PowerSeries κF :=
  (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).map
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom

/-- Returning through the original residue isomorphism gives the actual
prime-field coordinate, coefficient by coefficient. -/
theorem map_falseTateCoefficientCoordinate (g : FT ≃ₐ[Padic p] FT) :
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g).map
      (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).toRingHom =
      falseTatePowerSeriesCoordinate p hp₂ hπ u hu g := by
  ext n
  simp only [falseTateCoefficientCoordinate, PowerSeries.coeff_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

/-- The transported actual family has zero constant coefficient. -/
@[simp]
theorem falseTateCoefficientCoordinate_constantCoeff (g : FT ≃ₐ[Padic p] FT) :
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g).constantCoeff = 0 := by
  simpa only [falseTateCoefficientCoordinate, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, map_zero] using
    congrArg (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)

/-- Every transported linear coefficient remains a unit. -/
theorem falseTateCoefficientCoordinate_linear_isUnit (g : FT ≃ₐ[Padic p] FT) :
    IsUnit ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g).coeff 1) := by
  simpa only [falseTateCoefficientCoordinate, PowerSeries.coeff_map] using
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g).map
      (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom

/-- The entire transported family retains the actual reversed group law. -/
theorem falseTateCoefficientCoordinate_mul (g h : FT ≃ₐ[Padic p] FT) :
    falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (g * h) =
      (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu h).subst
        (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g) := by
  change (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g * h)).map _ = _
  rw [falseTatePowerSeriesCoordinate_mul]
  exact PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)) _

/-- Every actual group power is the genuine power-series iterate in the
original coefficient residue field. -/
theorem falseTateCoefficientCoordinate_pow (g : FT ≃ₐ[Padic p] FT) (n : ℕ) :
    falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (g ^ n) =
      powerSeriesIterate (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g) n := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  change HahnSeries.ofPowerSeries ℤ κF
    ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g ^ n)).map _) = _
  rw [← CoefficientRing.mapRingHom_ofPowerSeries, falseTatePowerSeriesCoordinate_pow]
  exact CoefficientRing.coefficient_map_iterate_variable
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g) n

/-- The residue-coordinate equation is the literal image of the original
norm-family uniformizer under the original group action. -/
theorem falseTateCoefficientCoordinate_eval (g : FT ≃ₐ[Padic p] FT) :
    letI := normLimitField (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
    falseTateNormFieldLaurentEquiv p hp₂ hπ u hu
      (mapRingHom (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).toRingHom
        (HahnSeries.ofPowerSeries ℤ κF
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g))) =
      normLimitAut (Padic p) p (isAPF_falseTateExtension p hπ)
        (not_finiteDimensional_falseTateExtension_padic p (π : Padic p)) g u := by
  let := normLimitField (Padic p) FT p (isAPF_falseTateExtension p hπ)
    (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
  rw [CoefficientRing.mapRingHom_ofPowerSeries, map_falseTateCoefficientCoordinate]
  exact falseTateNormFieldLaurentEquiv_powerSeriesCoordinate p hp₂ hπ u hu g

/-- The canonical Laurent substitution is the original conjugated false Tate
action on the entire Laurent field. Fraction-field uniqueness uses the already
proved equality on every power series and requires no change of topology. -/
theorem falseTatePowerSeriesSubstEquiv_apply (g : FT ≃ₐ[Padic p] FT)
    (A : LaurentSeries (ZMod p)) :
    powerSeriesSubstEquiv (0 : ZMod p) IsNilpotent.zero
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g) A =
      falseTateLaurentAction p hp₂ hπ u hu g A := by
  have heq : (powerSeriesSubstEquiv (0 : ZMod p) IsNilpotent.zero
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g)).toRingHom =
      (falseTateLaurentAction p hp₂ hπ u hu g).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries (ZMod p))
    intro B
    change powerSeriesSubstEquiv (0 : ZMod p) IsNilpotent.zero
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g)
      (HahnSeries.ofPowerSeries ℤ (ZMod p) B) =
      falseTateLaurentAction p hp₂ hπ u hu g (B : LaurentSeries (ZMod p))
    rw [powerSeriesSubstEquiv_apply, subst_ofPowerSeries (0 : ZMod p) IsNilpotent.zero
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g) B,
      falseTateLaurentAction_powerSeries]
  exact RingHom.congr_fun heq A

/-- Actual coefficient transport intertwines the actual original action with
canonical Laurent substitution at its actual coefficient-residue coordinate. -/
theorem falseTateCoefficientCoordinate_substitution (g : FT ≃ₐ[Padic p] FT)
    (A : LaurentSeries (ZMod p)) :
    mapRingHom (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
      (falseTateLaurentAction p hp₂ hπ u hu g A) =
      powerSeriesSubstEquiv (0 : κF) IsNilpotent.zero
        (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g)
        (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu g)
        (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu g)
        (mapRingHom
          (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom A) := by
  rw [← falseTatePowerSeriesSubstEquiv_apply]
  exact CoefficientRing.coefficient_map_coordinate
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g) A

/-- Every displacement order of every actual iterate is unchanged by the
original residue-coefficient transport. -/
theorem falseTateCoefficientCoordinate_iterate_displacement_order
    (g : FT ≃ₐ[Padic p] FT) (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g) n) -
      HahnSeries.single (1 : ℤ) 1).order =
      (HahnSeries.ofPowerSeries ℤ (ZMod p)
        (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (g ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order := by
  rw [falseTatePowerSeriesCoordinate_pow]
  exact CoefficientRing.order_mapped_iterate_displacement
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.injective
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu g)
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g) n

/-- Actual coefficient transport preserves the exact multiplicative order of
every original nonzero linear coefficient, regarded as its canonical unit. -/
theorem orderOf_falseTateCoefficientCoordinate_linear_unit (g : FT ≃ₐ[Padic p] FT) :
    orderOf (Units.mk0
      ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g).coeff 1)
      (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu g).ne_zero) =
      orderOf (Units.mk0
        ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).coeff 1)
        (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g).ne_zero) := by
  let ell := Units.mk0 ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).coeff 1)
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu g).ne_zero
  have heq : Units.mk0
      ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g).coeff 1)
      (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu g).ne_zero =
      Units.map
        (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toMonoidHom ell := by
    apply Units.ext
    rfl
  rw [heq]
  exact CoefficientRing.order_units_coefficient_map
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.injective ell

/-- The actual Kummer coordinate is tangent to the identity over the actual
coefficient residue field. -/
theorem falseTateCoefficientCoordinate_tau_coeff_one :
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val).coeff 1 = 1 := by
  simp only [falseTateCoefficientCoordinate, PowerSeries.coeff_map,
    falseTatePowerSeriesCoordinate_tau_coeff_one, map_one]

/-- The exact actual Kummer ramification numbers survive coefficient transport. -/
theorem falseTateCoefficientCoordinate_tau_ramification_order (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
          (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1 =
      (kummerRamificationBreak p n : ℤ) := by
  rw [falseTateCoefficientCoordinate_iterate_displacement_order]
  rw [laurent_displacement_order_of_powerSeries_order _ (kummerRamificationBreak p n + 1)
    (falseTatePowerSeriesCoordinate_tau_pow_order p hp₂ hπ u hu n)]
  simp

/-- The canonical substitution at the actual Kummer coordinate has infinite
order, derived from the original action profile rather than assumed. -/
theorem falseTateCoefficientCoordinate_tau_infiniteOrder :
    ¬ IsOfFinOrder (powerSeriesSubstEquiv (0 : κF) IsNilpotent.zero
      (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
      (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
      (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _)) := by
  have hinf : ¬ IsOfFinOrder (powerSeriesSubstEquiv (0 : ZMod p) IsNilpotent.zero
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val)
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu _)) := by
    intro hfinite
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfinite
    apply falseTatePowerSeriesCoordinate_tau_infiniteOrder p hp₂ hπ u hu n hn
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [← show powerSeriesIterate
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val) n =
      (PowerSeries.subst (falseTatePowerSeriesCoordinate p hp₂ hπ u hu
        (tau p hp₂ hπ).val))^[n] PowerSeries.X from rfl]
    rw [ofPowerSeries_powerSeriesIterate _
      (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _)
      (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu _),
      HahnSeries.ofPowerSeries_X, ← AlgEquiv.coe_pow, hpow]
    rfl
  exact CoefficientRing.infinite_order_mapped_coordinate
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.injective
    (falseTatePowerSeriesCoordinate p hp₂ hπ u hu (tau p hp₂ hπ).val)
    (falseTatePowerSeriesCoordinate_constantCoeff p hp₂ hπ u hu _)
    (falseTatePowerSeriesCoordinate_linear_isUnit p hp₂ hπ u hu _) hinf

/-- The actual tame linear coefficient has exact unit-group order `p - 1`
in the original coefficient residue field. -/
theorem orderOf_falseTateCoefficientCoordinate_tame_linear_unit :
    orderOf (Units.mk0
      ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu
        (tameGenerator p hp₂ hπ).val).coeff 1)
      (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _).ne_zero) =
      p - 1 := by
  rw [orderOf_falseTateCoefficientCoordinate_linear_unit]
  exact orderOf_falseTatePowerSeriesCoordinate_tameGenerator_linear_unit p hp₂ hπ u hu

/-- The actual coefficient-residue ramification orders have the required
prime divisibility. -/
theorem falseTateCoefficientCoordinate_tau_ramification_dvd (n : ℕ) :
    (p : ℤ) ∣
      ((HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
          (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1) + 1 := by
  rw [falseTateCoefficientCoordinate_tau_ramification_order]
  exact_mod_cast kummerRamificationBreak_succ_dvd p n

/-- The actual coefficient-residue ramification orders satisfy the stronger
growth estimate used by the finite obstruction. -/
theorem falseTateCoefficientCoordinate_tau_ramification_growth (n : ℕ) :
    ((p : ℤ) + 1) *
      ((HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
          (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
          (p ^ (n + 1))) - HahnSeries.single (1 : ℤ) 1).order - 1 := by
  rw [falseTateCoefficientCoordinate_tau_ramification_order,
    falseTateCoefficientCoordinate_tau_ramification_order]
  exact_mod_cast kummerRamificationBreak_growth p n (Fact.out : p.Prime).two_le

/-- The actual integer order sequence has precisely the prescribed p-adic limit. -/
theorem falseTateCoefficientCoordinate_tau_ramification_tendsto :
    Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ κF
        (powerSeriesIterate
          (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
          (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
      (nhds (kummerRamificationLimit p)) := by
  simpa only [falseTateCoefficientCoordinate_tau_ramification_order, Int.cast_natCast] using
    kummerRamificationBreak_tendsto_padic p

/-- The actual three-element obstruction occurs at one power beyond the
original coefficient valuation of `p`, for every original norm-field uniformizer. -/
theorem falseTate_finite_obstruction (ϖ : O_F) (hϖ : Irreducible ϖ) :
    let f := falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu
    ∃ e : ℕ, IsDiscreteValuationRing.addVal O_F (p : O_F) = e ∧
      ∀ (P : LaurentSeries (CoefficientRing.Truncation ϖ (e + 1)))
        (hP : mapRingHom (CoefficientRing.residue ϖ hϖ (e + 1) (by omega)) P =
          HahnSeries.single (p : ℤ) 1)
        (G D : LaurentSeries (CoefficientRing.Truncation ϖ (e + 1)))
        (hG : mapRingHom (CoefficientRing.residue ϖ hϖ (e + 1) (by omega)) G =
          HahnSeries.ofPowerSeries ℤ κF (f (tau p hp₂ hπ).val))
        (hD : mapRingHom (CoefficientRing.residue ϖ hϖ (e + 1) (by omega)) D =
          HahnSeries.ofPowerSeries ℤ κF (f (tameGenerator p hp₂ hπ).val)),
        CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) P
          (CoefficientRing.frobeniusLift_isAdmissible ϖ hϖ p (e + 1) (by omega) P hP) G =
          CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) G
            (CoefficientRing.isAdmissible_of_residue_powerSeries ϖ hϖ (e + 1) (by omega) G
              (f (tau p hp₂ hπ).val)
              (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
              (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _) hG) P →
        CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) P
          (CoefficientRing.frobeniusLift_isAdmissible ϖ hϖ p (e + 1) (by omega) P hP) D =
          CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) D
            (CoefficientRing.isAdmissible_of_residue_powerSeries ϖ hϖ (e + 1) (by omega) D
              (f (tameGenerator p hp₂ hπ).val)
              (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
              (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _) hD) P →
        False := by
  let : CharP κF p := CoefficientRing.coefficientExtensionResidue_charP p F htotal
  obtain ⟨e, a, hpe, he⟩ := CoefficientRing.coefficientExtension_exists_p_factor p F ϖ hϖ
  refine ⟨e, he, ?_⟩
  intro P hP G D hG hD hcommG hcommD
  let ell := Units.mk0
    ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu
      (tameGenerator p hp₂ hπ).val).coeff 1)
    (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _).ne_zero
  exact CoefficientRing.not_commuting_finite_lifts_of_numerical_ramification ϖ hϖ p e
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal) a a.isUnit hpe
    P hP G D
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tameGenerator p hp₂ hπ).val)
    (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
    (falseTateCoefficientCoordinate_tau_coeff_one p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
    ell rfl (orderOf_falseTateCoefficientCoordinate_tame_linear_unit p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_infiniteOrder p hp₂ hπ F htotal u hu) hG hD
    (falseTateCoefficientCoordinate_tau_ramification_dvd p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_growth p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_tendsto p hp₂ hπ F htotal u hu)
    hcommG hcommD

/-- The actual coordinate family of every original false Tate uniformizer has
no completed lift over any finite totally ramified coefficient extension.
The intrinsic public Theorem A will hide these coordinates in `BergerLiftable`. -/
theorem falseTateCoordinateFamily_not_liftable (ϖ : O_F) (hϖ : Irreducible ϖ) :
    letI : Fintype κF := Fintype.ofEquiv (ZMod p)
      (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toEquiv
    ¬ CoefficientRing.Liftable ϖ hϖ
      (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu)
      (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu)
      (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu) := by
  let ell := Units.mk0
    ((falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu
      (tameGenerator p hp₂ hπ).val).coeff 1)
    (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _).ne_zero
  exact CoefficientRing.coefficientExtension_not_liftable_of_numerical_ramification p F htotal
    ϖ hϖ (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu)
    (tau p hp₂ hπ).val (tameGenerator p hp₂ hπ).val
    (falseTateCoefficientCoordinate_tau_coeff_one p hp₂ hπ F htotal u hu)
    ell rfl (orderOf_falseTateCoefficientCoordinate_tame_linear_unit p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_infiniteOrder p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_dvd p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_growth p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_tendsto p hp₂ hπ F htotal u hu)

local instance theoremAIntegralClosureLocalHom :
    IsLocalHom (algebraMap O_0 (integralClosure O_0 FT)) :=
  integralClosure_algebraMap_isLocalHom (Padic p) (L := FT)

include hp₂ hπ in
/-- The actual base residue map onto the integral-closure residue of the
odd-prime false Tate extension is surjective. -/
theorem falseTate_integralClosureResidue_surjective : Function.Surjective
    (algebraMap (IsLocalRing.ResidueField O_0)
      (IsLocalRing.ResidueField (integralClosure O_0 FT))) := by
  intro x
  let e := integralClosureSpectralResidueEquiv (Padic p) (L := FT)
  obtain ⟨a, ha⟩ := falseTateExtension_residue_algebraMap_surjective p hp₂ hπ (e x)
  refine ⟨a, e.injective ?_⟩
  exact (e.commutes a).trans ha

private theorem laurent_valuation_map_equiv {k k' : Type*} [Field k] [Field k']
    (ε : k ≃+* k') (A : LaurentSeries k) :
    (Valued.v (mapRingHom ε.toRingHom A) : WithZero (Multiplicative ℤ)) = Valued.v A := by
  by_cases hA : A = 0
  · simp [hA]
  have hm : mapRingHom ε.toRingHom A ≠ 0 := by
    simpa only [map_zero] using (mapRingHom ε.toRingHom).injective.ne hA
  have hv : (Valued.v A : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hA
  have hvm : (Valued.v (mapRingHom ε.toRingHom A) : WithZero (Multiplicative ℤ)) ≠ 0 := by
    simpa using hm
  apply le_antisymm
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k' hv).mpr
    intro n hn
    have hz := (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k hv).mp le_rfl n hn
    simp only [mapRingHom_coeff, hz, map_zero]
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k hvm).mpr
    intro n hn
    have hz := (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k' hvm).mp le_rfl n hn
    apply ε.injective
    simpa only [mapRingHom_coeff, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_zero] using hz

private theorem sourceLaurent_falseTate_constant (a : ZMod p) :
    letI := normLimitField (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
    normLimitLaurentEquiv (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p)) u hu
      (HahnSeries.C ((falseTateResidueEquiv p hp₂ hπ).symm a)) =
      (falseTateNormCoefficients p hp₂ hπ a : NormLimit (Padic p) FT) := by
  let := normLimitField (Padic p) FT p (isAPF_falseTateExtension p hπ)
    (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
  have hc := normLimitLaurentEquiv_C (Padic p) FT p (isAPF_falseTateExtension p hπ)
    (not_finiteDimensional_falseTateExtension_padic p (π : Padic p)) u hu
    ((falseTateResidueEquiv p hp₂ hπ).symm a)
  erw [LaurentSeries.algebraMap_apply] at hc
  exact hc

private theorem mapRingHom_powerSeries_X {k k' : Type*} [Field k] [Field k']
    (ψ : k →+* k') :
    mapRingHom ψ (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) =
      algebraMap (PowerSeries k') (LaurentSeries k') PowerSeries.X := by
  change mapRingHom ψ (HahnSeries.ofPowerSeries ℤ k PowerSeries.X) = _
  rw [CoefficientRing.mapRingHom_ofPowerSeries, PowerSeries.map_X]
  rfl

/-- The general source-residue Laurent evaluation and the already computed
prime-field evaluation are the same map after the actual residue isomorphism. -/
theorem normLimitLaurentEquiv_map_falseTateResidueEquiv (A : LaurentSeries (ZMod p)) :
    letI := normLimitField (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
    normLimitLaurentEquiv (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p)) u hu
      (mapRingHom (falseTateResidueEquiv p hp₂ hπ).symm.toRingHom A) =
      falseTateNormFieldLaurentEquiv p hp₂ hπ u hu A := by
  let hL := isAPF_falseTateExtension p hπ
  let hInfinite := not_finiteDimensional_falseTateExtension_padic p (π : Padic p)
  let := normLimitField (Padic p) FT p hL hInfinite
  let := normLimitValued (Padic p) FT p hL hInfinite
  let ε := (falseTateResidueEquiv p hp₂ hπ).symm
  let j : LaurentSeries (ZMod p) ≃+* LaurentSeries
      (IsLocalRing.ResidueField (integralClosure O_0 FT)) :=
    RingEquiv.ofBijective (mapRingHom ε.toRingHom)
      ⟨(mapRingHom ε.toRingHom).injective, mapRingHom_surjective _ ε.surjective⟩
  have hj : Continuous j :=
    (valuedRingEquiv_uniformContinuous j (laurent_valuation_map_equiv ε)).continuous
  let e := normLimitLaurentEquiv (Padic p) FT p hL hInfinite u hu
  have he := falseTateNormFieldLaurentEquiv_unique p hp₂ hπ u hu
    (e.toRingHom.comp j.toRingHom)
    ((continuous_normLimitLaurentEquiv (Padic p) FT p hL hInfinite u hu).comp hj)
  have hC (a : ZMod p) : (e.toRingHom.comp j.toRingHom)
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a) =
        (falseTateNormCoefficients p hp₂ hπ a : NormLimit (Padic p) FT) := by
    change e (mapRingHom ε.toRingHom
      (algebraMap (ZMod p) (LaurentSeries (ZMod p)) a)) = _
    rw [LaurentSeries.algebraMap_apply, mapRingHom_C]
    exact sourceLaurent_falseTate_constant p hp₂ hπ u hu a
  have hX : (e.toRingHom.comp j.toRingHom)
      (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) = u := by
    exact (congrArg e (mapRingHom_powerSeries_X ε.toRingHom)).trans
      (normLimitLaurentEquiv_X (Padic p) FT p hL hInfinite u hu)
  exact congrArg (fun f => f A) (he hC hX)

/-- The intrinsic source-residue coordinate is exactly the computed original
prime-field coordinate under the original residue identification. -/
theorem sourceNormFieldCoordinate_falseTate [IsGalois (Padic p) FT]
    (g : FT ≃ₐ[Padic p] FT) :
    sourceNormFieldCoordinate (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p)) u hu g =
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).map
        (falseTateResidueEquiv p hp₂ hπ).symm.toRingHom := by
  let hL := isAPF_falseTateExtension p hπ
  let hInfinite := not_finiteDimensional_falseTateExtension_padic p (π : Padic p)
  let := normLimitField (Padic p) FT p hL hInfinite
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  apply (normLimitLaurentEquiv (Padic p) FT p hL hInfinite u hu).injective
  have he := normLimitLaurentEquiv_map_falseTateResidueEquiv p hp₂ hπ u hu
    (HahnSeries.ofPowerSeries ℤ (ZMod p)
      (falseTatePowerSeriesCoordinate p hp₂ hπ u hu g))
  rw [CoefficientRing.mapRingHom_ofPowerSeries] at he
  exact (sourceNormFieldCoordinate_eval (Padic p) FT p hL hInfinite u hu g).trans
    ((falseTateNormFieldLaurentEquiv_powerSeriesCoordinate p hp₂ hπ u hu g).symm.trans he.symm)

/-- For the prime residue field, every compatible internal residue
identification gives the same actual coefficient family. -/
theorem bergerCoordinateFamily_falseTate [IsGalois (Padic p) FT]
    (ε : κF ≃+* IsLocalRing.ResidueField O_0) (g : FT ≃ₐ[Padic p] FT) :
    bergerCoordinateFamily (Padic p) FT p (isAPF_falseTateExtension p hπ)
      (not_finiteDimensional_falseTateExtension_padic p (π : Padic p))
      (falseTate_integralClosureResidue_surjective p hp₂ hπ) u hu F ε g =
      falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu g := by
  let ψ : ZMod p →+* κF := ε.symm.toRingHom.comp
    ((normFieldBaseResidueEquiv (Padic p) FT
      (falseTate_integralClosureResidue_surjective p hp₂ hπ)).symm.toRingHom.comp
        (falseTateResidueEquiv p hp₂ hπ).symm.toRingHom)
  have hψ : ψ = (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal).symm.toRingHom :=
    Subsingleton.elim _ _
  simp only [bergerCoordinateFamily, normFieldCoordinate,
    sourceNormFieldCoordinate_falseTate p hp₂ hπ u hu g, falseTateCoefficientCoordinate]
  ext n
  erw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
    PowerSeries.coeff_map]
  exact congrArg (fun φ : ZMod p →+* κF =>
    φ ((falseTatePowerSeriesCoordinate p hp₂ hπ u hu g).coeff n)) hψ

private theorem liftable_of_family_eq {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (ϖ : O) (hϖ : Irreducible ϖ) {Γ : Type*} [Group Γ]
    (f f' : Γ → PowerSeries (IsLocalRing.ResidueField O))
    (hz : ∀ g, (f g).constantCoeff = 0) (hl : ∀ g, IsUnit ((f g).coeff 1))
    (hz' : ∀ g, (f' g).constantCoeff = 0) (hl' : ∀ g, IsUnit ((f' g).coeff 1))
    (h : f = f') : CoefficientRing.Liftable ϖ hϖ f hz hl →
      CoefficientRing.Liftable ϖ hϖ f' hz' hl' := by
  subst f'
  exact id

include hp₂ hπ htotal in
/-- Theorem A: the actual odd-prime false Tate extension is not Berger
liftable over any finite totally ramified coefficient extension. All coordinate
and uniformizer choices are internal to the intrinsic public predicate. -/
theorem falseTate_not_bergerLiftable :
    letI := falseTateExtension_isGalois p (π : Padic p)
      (fun h => hπ.ne_zero (Subtype.ext h))
    letI : Fact (IsAPF (Padic p) FT) := ⟨isAPF_falseTateExtension p hπ⟩
    letI : Fact (¬ Module.Finite (Padic p) FT) :=
      ⟨not_finiteDimensional_falseTateExtension_padic p (π : Padic p)⟩
    ¬ @BergerLiftable p _ (Padic p) _ _ _ _ _ _ FT _ _ _ _ _
      ⟨falseTate_integralClosureResidue_surjective p hp₂ hπ⟩ F _ _ _ := by
  let := falseTateExtension_isGalois p (π : Padic p)
    (fun h => hπ.ne_zero (Subtype.ext h))
  let hL := isAPF_falseTateExtension p hπ
  let hInfinite := not_finiteDimensional_falseTateExtension_padic p (π : Padic p)
  let hres := falseTate_integralClosureResidue_surjective p hp₂ hπ
  let : Fact (IsAPF (Padic p) FT) := ⟨hL⟩
  let : Fact (¬ Module.Finite (Padic p) FT) := ⟨hInfinite⟩
  let : Fact (Function.Surjective
      (algebraMap (IsLocalRing.ResidueField O_0)
        (IsLocalRing.ResidueField (integralClosure O_0 FT)))) := ⟨hres⟩
  let : Finite κF := bergerCoefficientResidue_finite p F
  let u₀ := normLimitUniformizer (Padic p) FT p hL hInfinite
  let hu₀ := normLimitValuation_normLimitUniformizer (Padic p) FT p hL hInfinite
  intro h
  obtain ⟨ε, ϖ, hϖ, hLift⟩ := h
  have hfamily : bergerCoordinateFamily (Padic p) FT p hL hInfinite hres u₀ hu₀ F ε =
      falseTateCoefficientCoordinate p hp₂ hπ F htotal u₀ hu₀ := by
    funext g
    exact bergerCoordinateFamily_falseTate p hp₂ hπ F htotal u₀ hu₀ ε g
  have hnot := falseTateCoordinateFamily_not_liftable p hp₂ hπ F htotal u₀ hu₀ ϖ hϖ
  exact hnot (liftable_of_family_eq ϖ hϖ _ _ _ _ _ _ hfamily hLift)

end FalseTateNonliftability
