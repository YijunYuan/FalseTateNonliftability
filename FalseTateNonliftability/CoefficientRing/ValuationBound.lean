/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative

/-!
# Valuation bound at the highest normalized derivative level

The actual near-identity Laurent substitution and its first-order remainder
bound the order of a normalized derivative at its highest coefficient level.
All support estimates use the original Laurent series, including negative
orders. The final specialization uses the actual spectral integers of a
finite totally ramified extension of `ℚ_[p]`.

This proves blueprint theorem `nl:valuation-bound`.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

variable {R : Type*} [CommRing R]

/-- Positive powers preserve an actual lower bound on the difference from
one. The auxiliary factors remain in the nonnegative support subgroup. -/
theorem pow_sub_one_mem_orderAddSubgroup (x : LaurentSeries R) (m : ℤ) (hm : 0 ≤ m)
    (hx : x - 1 ∈ orderAddSubgroup m) (n : ℕ) :
    x ^ n - 1 ∈ orderAddSubgroup m := by
  have hone : (1 : LaurentSeries R) ∈ orderAddSubgroup 0 := by
    simpa only [map_one] using ofPowerSeries_mem_orderAddSubgroup_zero (1 : PowerSeries R)
  have hx0 : x ∈ orderAddSubgroup 0 := by
    simpa only [sub_add_cancel] using
      (orderAddSubgroup 0).add_mem (orderAddSubgroup_antitone hm hx) hone
  induction n with
  | zero => simp only [pow_zero, sub_self, zero_mem]
  | succ n ih =>
    have hmul : (x ^ n - 1) * x ∈ orderAddSubgroup m := by
      simpa only [add_zero] using mul_mem_orderAddSubgroup ih hx0
    have heq : x ^ (n + 1) - 1 = (x ^ n - 1) * x + (x - 1) := by
      rw [pow_succ]
      ring
    rw [heq]
    exact (orderAddSubgroup m).add_mem hmul hx

/-- In characteristic `p`, the displayed normal form and `p ∣ d+1`
force the actual derivative to differ from one only in degree at least `2*d`. -/
theorem derivative_sub_one_mem_of_normalForm (p : ℕ) [CharP R p]
    (g : LaurentSeries R) (d : ℤ) (hdiv : (p : ℤ) ∣ d + 1) (α : R)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    derivative R g - 1 ∈ orderAddSubgroup (2 * d) := by
  have hcast : ((d + 1 : ℤ) : R) = 0 := by
    obtain ⟨n, hn⟩ := hdiv
    rw [hn, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero R p, zero_mul]
  simpa [hcast] using derivative_mem_orderAddSubgroup (2 * d + 1)
    (g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α) hg

/-- The normal-form tail gives the actual lower bound on the displacement. -/
theorem sub_variable_mem_of_normalForm (g : LaurentSeries R) (d : ℤ) (hd : 1 ≤ d) (α : R)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
  mem_orderAddSubgroup_of_sub_single_mem _ (d + 1) α
    (orderAddSubgroup_antitone (by omega) hg)

/-- The linear coefficient is one as a consequence of the normal form. -/
theorem coeff_one_eq_one_of_normalForm (g : LaurentSeries R) (d : ℤ) (hd : 1 ≤ d) (α : R)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) : g.coeff 1 = 1 := by
  have hc := (mem_orderAddSubgroup_iff_coeff (d + 1) _).mp
    (sub_variable_mem_of_normalForm g d hd α hg) 1 (by omega)
  simpa only [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] using hc

section Field

variable {k : Type*} [Field k]

local instance valuationBoundZeroSpanIsMaximal : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual commuting chain equation and the controlled Laurent Taylor
remainder imply the top-level order bound. The input order may be negative. -/
theorem order_le_of_subst_eq_derivative_pow_mul (p : ℕ) [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1) (α : k) (hα : α ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1))
    (h : LaurentSeries k) (hD : derivative k h ≠ 0)
    (hDorder : (derivative k h).order ≤ (p : ℤ) - 2)
    (hchain : subst 0 IsNilpotent.zero g hG h = (derivative k g) ^ (p - 1) * h) :
    h.order ≤ (p : ℤ) - 1 - d := by
  have htail : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 1 + 1) := orderAddSubgroup_antitone (by omega) hg
  have hδ : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
    mem_orderAddSubgroup_of_sub_single_mem _ (d + 1) α htail
  have hδorder : (g - HahnSeries.single (1 : ℤ) 1).order = d + 1 :=
    order_eq_of_sub_single_mem _ (d + 1) α hα htail
  have hδne : g - HahnSeries.single (1 : ℤ) 1 ≠ 0 := by
    intro hz
    have ho := hδorder
    rw [hz, HahnSeries.order_zero] at ho
    omega
  have hpow := pow_sub_one_mem_orderAddSubgroup (derivative k g) (2 * d) (by omega)
    (derivative_sub_one_mem_of_normalForm p g d hdiv α hg) (p - 1)
  have hdiff : subst 0 IsNilpotent.zero g hG h - h ∈
      orderAddSubgroup (h.order + 2 * d) := by
    rw [hchain]
    have heq : (derivative k g) ^ (p - 1) * h - h =
        ((derivative k g) ^ (p - 1) - 1) * h := by ring
    rw [heq]
    simpa only [add_comm] using mul_mem_orderAddSubgroup hpow (mem_orderAddSubgroup_order h)
  have htaylor := subst_taylor_mem_orderAddSubgroup g hG d hd hδ h.order h
    (mem_orderAddSubgroup_order h)
  have hprod : (g - HahnSeries.single (1 : ℤ) 1) * derivative k h ∈
      orderAddSubgroup (h.order + 2 * d) := by
    have heq : (subst 0 IsNilpotent.zero g hG h - h) -
        (subst 0 IsNilpotent.zero g hG h - h -
          (g - HahnSeries.single (1 : ℤ) 1) * derivative k h) =
        (g - HahnSeries.single (1 : ℤ) 1) * derivative k h := by ring
    rw [← heq]
    exact (orderAddSubgroup _).sub_mem hdiff htaylor
  have hbound : h.order + 2 * d ≤
      ((g - HahnSeries.single (1 : ℤ) 1) * derivative k h).order := by
    change ((h.order + 2 * d : ℤ) : WithTop ℤ) ≤
      ((g - HahnSeries.single (1 : ℤ) 1) * derivative k h).orderTop at hprod
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hδne hD)] at hprod
    exact_mod_cast hprod
  rw [HahnSeries.order_mul hδne hD, hδorder] at hbound
  omega

end Field

end LaurentSeries

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

section DiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (π : O) (hπ : Irreducible π)

local instance valuationBoundResidueZeroSpanIsMaximal :
    (Ideal.span ({(0 : IsLocalRing.ResidueField O)} : Set (IsLocalRing.ResidueField O))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- A normal form in the actual residue field supplies admissibility in the
original finite coefficient quotient. -/
theorem isAdmissible_of_residue_normalForm (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (d : ℤ) (hd : 1 ≤ d)
    (α : IsLocalRing.ResidueField O)
    (hg : mapRingHom (residue π hπ r hr) G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1)) :
    IsAdmissible (parameter π r) G := by
  rw [isAdmissible_iff_actualResidue π hπ r hr G]
  exact (isAdmissible_zero_iff _).mp
    (isAdmissible_of_sub_variable_mem _ d hd (sub_variable_mem_of_normalForm _ d hd α hg))

/-- The valuation bound for the actual highest normalized derivative of a
finite Frobenius lift. Its derivative bound and chain equation are proved
producers; admissibility and the linear coefficient follow from the normal form. -/
theorem order_normalizedDerivative_le_of_top (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP = e)
    (G : LaurentSeries (Truncation π (e + 1)))
    (d : ℤ) (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1)
    (α : IsLocalRing.ResidueField O) (hα : α ≠ 0)
    (hg : mapRingHom (residue π hπ (e + 1) (by omega)) G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1))
    (hcomm : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G
        (isAdmissible_of_residue_normalForm π hπ (e + 1) (by omega) G d hd α hg) P) :
    (normalizedDerivative π hπ p e u hu hpe P hP).order ≤ (p : ℤ) - 1 - d := by
  let g := mapRingHom (residue π hπ (e + 1) (by omega)) G
  have hG := isAdmissible_of_residue_normalForm π hπ (e + 1) (by omega) G d hd α hg
  have hlinear : g.coeff 1 ≠ 0 := by
    rw [coeff_one_eq_one_of_normalForm g d hd α hg]
    exact one_ne_zero
  have hchain := normalizedDerivative_commuting_substitution π hπ p e ε u hu hpe P hP
    G hG hlinear hcomm
  have hD := derivative_normalizedDerivative_ne_zero_and_order_le_of_eq π hπ p e
    u hu hpe P hP hs
  exact order_le_of_subst_eq_derivative_pow_mul p g
    (isAdmissible_residue π hπ (e + 1) (by omega) G hG) d hd hdiv α hα hg
    (normalizedDerivative π hπ p e u hu hpe P hP) hD.1 hD.2 hchain

/-- A Frobenius residue supplies actual admissibility in the original
canonical completion. -/
theorem completedFrobeniusLift_isAdmissible (p : ℕ) [Fact p.Prime]
    (P : PrincipalCompletion π)
    (hP : completedResidue π hπ P = HahnSeries.single (p : ℤ) 1) :
    CompletedIsAdmissible π hπ P := by
  rw [CompletedIsAdmissible, hP]
  refine ⟨(p : ℤ), by exact_mod_cast (Fact.out : p.Prime).pos, ?_⟩
  simp

/-- The residue normal form also supplies actual completed admissibility;
there is no extra substitution-existence hypothesis. -/
theorem completedIsAdmissible_of_residue_normalForm (G : PrincipalCompletion π)
    (d : ℤ) (hd : 1 ≤ d) (α : IsLocalRing.ResidueField O)
    (hg : completedResidue π hπ G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1)) :
    CompletedIsAdmissible π hπ G := by
  exact (isAdmissible_zero_iff _).mp
    (isAdmissible_of_sub_variable_mem _ d hd (sub_variable_mem_of_normalForm _ d hd α hg))

/-- The source valuation bound for commuting elements of the same actual
principal completion. Normalization is performed only in the actual finite
coordinate `e+1`; commutation descends through its proved coordinate bridge. -/
theorem completed_order_normalizedDerivative_le_of_top (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : PrincipalCompletion π)
    (hP : completedResidue π hπ P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe (completedPrincipalReduction π (e + 1) P)
      ((completedResidue_eq π hπ (e + 1) (by omega) P).symm.trans hP) = e)
    (G : PrincipalCompletion π) (d : ℤ) (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1)
    (α : IsLocalRing.ResidueField O) (hα : α ≠ 0)
    (hg : completedResidue π hπ G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1))
    (hcomm : completedSubst π hπ P (completedFrobeniusLift_isAdmissible π hπ p P hP) G =
      completedSubst π hπ G (completedIsAdmissible_of_residue_normalForm π hπ G d hd α hg) P) :
    (normalizedDerivative π hπ p e u hu hpe (completedPrincipalReduction π (e + 1) P)
      ((completedResidue_eq π hπ (e + 1) (by omega) P).symm.trans hP)).order ≤
        (p : ℤ) - 1 - d := by
  have hg' : mapRingHom (residue π hπ (e + 1) (by omega))
      (completedPrincipalReduction π (e + 1) G) - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1) := by
    rw [← completedResidue_eq π hπ (e + 1) (by omega) G]
    exact hg
  have hc := congrArg (completedPrincipalReduction π (e + 1)) hcomm
  simp only [completedPrincipalReduction_completedSubst π hπ _ _ (e + 1) (by omega)] at hc
  exact order_normalizedDerivative_le_of_top π hπ p e ε u hu hpe
    (completedPrincipalReduction π (e + 1) P)
    ((completedResidue_eq π hπ (e + 1) (by omega) P).symm.trans hP) hs
    (completedPrincipalReduction π (e + 1) G) d hd hdiv α hα hg' hc

end DiscreteValuationRing

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
  [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F
local notation "O_0" => Valuation.valuationSubring (NormedField.valuation (K := Padic p))

/-- The actual finite totally ramified coefficient extension satisfies the
source valuation bound in its original Laurent completion. The actual
exponent `vπ(p)`, unit factor, residue characteristic, and prime residue
equivalence are all supplied by the original spectral integer ring. -/
theorem coefficientExtension_order_normalizedDerivative_le_of_top
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) (π : O_F) (hπ : Irreducible π) :
    let : CharP (IsLocalRing.ResidueField O_F) p := coefficientExtensionResidue_charP p F htotal
    ∃ (e : ℕ) (u : O_Fˣ) (hpe : (p : O_F) = π ^ e * (u : O_F)),
      IsDiscreteValuationRing.addVal O_F (p : O_F) = e ∧
      ∀ (P : PrincipalCompletion π)
        (hP : completedResidue π hπ P = HahnSeries.single (p : ℤ) 1),
        derivativeLevel π hπ p e u u.isUnit hpe (completedPrincipalReduction π (e + 1) P)
          ((completedResidue_eq π hπ (e + 1) (by omega) P).symm.trans hP) = e →
        ∀ (G : PrincipalCompletion π) (d : ℤ) (hd : 1 ≤ d), (p : ℤ) ∣ d + 1 →
        ∀ (α : IsLocalRing.ResidueField O_F), α ≠ 0 →
        ∀ (hg : completedResidue π hπ G - HahnSeries.single (1 : ℤ) 1 -
            HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1)),
          completedSubst π hπ P (completedFrobeniusLift_isAdmissible π hπ p P hP) G =
            completedSubst π hπ G
              (completedIsAdmissible_of_residue_normalForm π hπ G d hd α hg) P →
          (normalizedDerivative π hπ p e u u.isUnit hpe (completedPrincipalReduction π (e + 1) P)
            ((completedResidue_eq π hπ (e + 1) (by omega) P).symm.trans hP)).order ≤
              (p : ℤ) - 1 - d := by
  let := coefficientExtensionResidue_charP p F htotal
  obtain ⟨e, u, hpe, he⟩ := coefficientExtension_exists_p_factor p F π hπ
  refine ⟨e, u, hpe, he, ?_⟩
  intro P hP hs G d hd hdiv α hα hg hcomm
  exact completed_order_normalizedDerivative_le_of_top π hπ p e
    (coefficientExtensionPrimeResidueEquiv p F htotal) u u.isUnit hpe P hP hs
    G d hd hdiv α hα hg hcomm

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing
