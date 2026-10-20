/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.FalseTate.TheoremA

/-!
# The top derivative level for the original false Tate Kummer action

Only a Frobenius lift and a commuting lift of the original Kummer generator
are used. The ramification profile is produced from the actual action, and the
coefficient exponent and unit are produced in the original spectral integer ring.

This implements `nl:top-level-obstruction`.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability

open FontaineWintenberger FalseTateExtension LaurentSeries

variable (p : ℕ) [Fact p.Prime]
  {π : (NormedField.valuation (K := Padic p)).valuationSubring}
  (hp₂ : p ≠ 2) (hπ : Irreducible π)
  (F : Type*) [Field F] [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]


variable (htotal : (IsLocalRing.maximalIdeal (spectralIntegerRing (Padic p) F)).ramificationIdx (Valuation.valuationSubring (NormedField.valuation (K := Padic p))) =
  Module.finrank (Padic p) F)
  (u : NormLimit (Padic p) (falseTateExtension p (π : Padic p)))
  (hu : normLimitValuation (Padic p) (falseTateExtension p (π : Padic p)) (isAPF_falseTateExtension p hπ) u =
    WithZero.exp (-1 : ℤ))

/-- For the actual original Kummer action, one commuting finite lift already
forces the Frobenius derivative level to be strictly below the original
coefficient valuation of `p`. All coefficient and action data are constructed. -/
theorem falseTate_derivativeLevel_lt (ϖ : (spectralIntegerRing (Padic p) F)) (hϖ : Irreducible ϖ) :
    letI : CharP (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) F)) p := CoefficientRing.coefficientExtensionResidue_charP p F htotal
    let f := falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val
    ∃ (e : ℕ) (a : (spectralIntegerRing (Padic p) F)ˣ) (hpe : (p : (spectralIntegerRing (Padic p) F)) = ϖ ^ e * a),
      IsDiscreteValuationRing.addVal (spectralIntegerRing (Padic p) F) (p : (spectralIntegerRing (Padic p) F)) = e ∧
      ∀ (P : LaurentSeries (CoefficientRing.Truncation ϖ (e + 1)))
        (hP : mapRingHom (CoefficientRing.residue ϖ hϖ (e + 1) (by omega)) P =
          HahnSeries.single (p : ℤ) 1)
        (G : LaurentSeries (CoefficientRing.Truncation ϖ (e + 1)))
        (hG : mapRingHom (CoefficientRing.residue ϖ hϖ (e + 1) (by omega)) G =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) F)) f),
        CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) P
            (CoefficientRing.frobeniusLift_isAdmissible ϖ hϖ p (e + 1) (by omega) P hP) G =
          CoefficientRing.truncatedSubst ϖ hϖ (e + 1) (by omega) G
            (CoefficientRing.isAdmissible_of_residue_powerSeries ϖ hϖ (e + 1) (by omega) G f
              (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
              (falseTateCoefficientCoordinate_linear_isUnit p hp₂ hπ F htotal u hu _) hG) P →
        CoefficientRing.derivativeLevel ϖ hϖ p e a a.isUnit hpe P hP < e := by
  let : CharP (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) F)) p := CoefficientRing.coefficientExtensionResidue_charP p F htotal
  obtain ⟨e, a, hpe, he⟩ := CoefficientRing.coefficientExtension_exists_p_factor p F ϖ hϖ
  refine ⟨e, a, hpe, he, ?_⟩
  intro P hP G hG hcomm
  exact CoefficientRing.derivativeLevel_lt_of_iterate_growth ϖ hϖ p e
    (CoefficientRing.coefficientExtensionPrimeResidueEquiv p F htotal) a a.isUnit hpe
    P hP G
    (falseTateCoefficientCoordinate p hp₂ hπ F htotal u hu (tau p hp₂ hπ).val)
    (falseTateCoefficientCoordinate_constantCoeff p hp₂ hπ F htotal u hu _)
    (falseTateCoefficientCoordinate_tau_coeff_one p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_infiniteOrder p hp₂ hπ F htotal u hu) hG
    (falseTateCoefficientCoordinate_tau_ramification_dvd p hp₂ hπ F htotal u hu)
    (falseTateCoefficientCoordinate_tau_ramification_growth p hp₂ hπ F htotal u hu) hcomm

end FalseTateNonliftability
