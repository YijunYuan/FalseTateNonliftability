module

public import FalseTateNonliftability.CoefficientRing.FiniteObstruction

/-!
# Completed and finite lifts of prescribed residue coordinates

These are the coefficient-ring lifting conditions of Yuan, Definition 1.1,
on the original canonical completion and its original positive quotients.
The residue-coordinate family is a parameter; its identification with an
actual field-of-norms action is a separate producer. The group law is
`S_(F g) (F h) = F (g*h)`, i.e. `F_h ∘ F_g = F_(gh)`.
-/

@[expose] public section

noncomputable section

open Filter Topology LaurentSeries
open scoped Topology

namespace FalseTateNonliftability.CoefficientRing

local instance liftabilityZeroSpanIsMaximal {k : Type*} [Field k] :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π)

/-- The actual residue power-series coordinate supplies completed
admissibility, without a separate substitution-existence assumption. -/
theorem completedIsAdmissible_of_residue_powerSeries (G : PrincipalCompletion π)
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0) (hlinear : IsUnit (f.coeff 1))
    (hres : completedResidue π hπ G = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) f) :
    CompletedIsAdmissible π hπ G := by
  rw [completedIsAdmissible_iff π hπ 1 le_rfl]
  exact isAdmissible_of_residue_powerSeries π hπ 1 le_rfl _ f hf hlinear hres

variable [hκ : Finite (IsLocalRing.ResidueField O)]

include hκ

/-- The Frobenius parameter uses the cardinality of the original finite
residue field, which is positive. -/
theorem completedIsAdmissible_of_residue_card_monomial (P : PrincipalCompletion π)
    (hP : completedResidue π hπ P = HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1) :
    CompletedIsAdmissible π hπ P := by
  rw [CompletedIsAdmissible, hP]
  exact ⟨(Nat.card (IsLocalRing.ResidueField O) : ℤ), by exact_mod_cast (Finite.card_pos (α := (IsLocalRing.ResidueField O))),
    HahnSeries.orderTop_single one_ne_zero⟩

/-- The same original residue Frobenius supplies admissibility in every
positive actual coefficient quotient. -/
theorem isAdmissible_of_residue_card_monomial (r : ℕ) (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r))
    (hP : mapRingHom (residue π hπ r hr) P = HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1) :
    IsAdmissible (parameter π r) P := by
  rw [isAdmissible_iff_actualResidue π hπ r hr P, hP]
  exact ⟨(Nat.card (IsLocalRing.ResidueField O) : ℤ), by exact_mod_cast (Finite.card_pos (α := (IsLocalRing.ResidueField O))),
    HahnSeries.orderTop_single one_ne_zero⟩

variable {Γ : Type*} [Group Γ]
  (f : Γ → PowerSeries (IsLocalRing.ResidueField O)) (hfzero : ∀ g, (f g).constantCoeff = 0)
  (hflinear : ∀ g, IsUnit ((f g).coeff 1))

/-- The actual completed lifting data for a prescribed residue-coordinate
family, with exactly the commutation and reversed composition laws of
Definition 1.1. No identity or inverse condition is added. -/
structure CompletedLift (f : Γ → PowerSeries (IsLocalRing.ResidueField O)) (hfzero : ∀ g, (f g).constantCoeff = 0)
    (hflinear : ∀ g, IsUnit ((f g).coeff 1)) where
  P : PrincipalCompletion π
  F : Γ → PrincipalCompletion π
  residue_P : completedResidue π hπ P = HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1
  residue_F : ∀ g, completedResidue π hπ (F g) = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) (f g)
  commute : ∀ g,
    completedSubst π hπ P (completedIsAdmissible_of_residue_card_monomial π hπ P residue_P) (F g) =
      completedSubst π hπ (F g)
        (completedIsAdmissible_of_residue_powerSeries π hπ (F g) (f g)
          (hfzero g) (hflinear g) (residue_F g)) P
  composition : ∀ g h,
    completedSubst π hπ (F g)
        (completedIsAdmissible_of_residue_powerSeries π hπ (F g) (f g)
          (hfzero g) (hflinear g) (residue_F g)) (F h) = F (g * h)

/-- The identical lifting equations in an actual positive coefficient
quotient; both the entire family and its composition law are retained. -/
structure FiniteLift (f : Γ → PowerSeries (IsLocalRing.ResidueField O)) (hfzero : ∀ g, (f g).constantCoeff = 0)
    (hflinear : ∀ g, IsUnit ((f g).coeff 1)) (r : ℕ) (hr : 1 ≤ r) where
  P : LaurentSeries (Truncation π r)
  F : Γ → LaurentSeries (Truncation π r)
  residue_P : mapRingHom (residue π hπ r hr) P = HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1
  residue_F : ∀ g, mapRingHom (residue π hπ r hr) (F g) = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) (f g)
  commute : ∀ g,
    truncatedSubst π hπ r hr P (isAdmissible_of_residue_card_monomial π hπ r hr P residue_P) (F g) =
      truncatedSubst π hπ r hr (F g)
        (isAdmissible_of_residue_powerSeries π hπ r hr (F g) (f g)
          (hfzero g) (hflinear g) (residue_F g)) P
  composition : ∀ g h,
    truncatedSubst π hπ r hr (F g)
        (isAdmissible_of_residue_powerSeries π hπ r hr (F g) (f g)
          (hfzero g) (hflinear g) (residue_F g)) (F h) = F (g * h)

/-- Liftability is existence of the actual completed data above. -/
def Liftable : Prop := Nonempty (CompletedLift π hπ f hfzero hflinear)

/-- Finite liftability is existence in the original positive quotient. -/
def FiniteLiftable (r : ℕ) (hr : 1 ≤ r) : Prop :=
  Nonempty (FiniteLift π hπ f hfzero hflinear r hr)

namespace CompletedLift

/-- Every positive actual coefficient coordinate preserves the complete
lifting data, including the reversed law for the entire group family. -/
def reduce (L : CompletedLift π hπ f hfzero hflinear) (r : ℕ) (hr : 1 ≤ r) :
    FiniteLift π hπ f hfzero hflinear r hr where
  P := completedPrincipalReduction π r L.P
  F g := completedPrincipalReduction π r (L.F g)
  residue_P := (completedResidue_eq π hπ r hr L.P).symm.trans L.residue_P
  residue_F g := (completedResidue_eq π hπ r hr (L.F g)).symm.trans (L.residue_F g)
  commute g := by
    have heq := congrArg (completedPrincipalReduction π r) (L.commute g)
    simpa only [completedPrincipalReduction_completedSubst π hπ _ _ r hr] using heq
  composition g h := by
    have heq := congrArg (completedPrincipalReduction π r) (L.composition g h)
    simpa only [completedPrincipalReduction_completedSubst π hπ _ _ r hr] using heq

@[simp]
theorem reduce_P (L : CompletedLift π hπ f hfzero hflinear) (r : ℕ) (hr : 1 ≤ r) :
    (L.reduce π hπ f hfzero hflinear r hr).P = completedPrincipalReduction π r L.P := rfl

@[simp]
theorem reduce_F (L : CompletedLift π hπ f hfzero hflinear) (r : ℕ) (hr : 1 ≤ r) (g : Γ) :
    (L.reduce π hπ f hfzero hflinear r hr).F g = completedPrincipalReduction π r (L.F g) := rfl

end CompletedLift

/-- Existence of actual completed lifting data implies existence at every
positive finite level. -/
theorem Liftable.finite (hL : Liftable π hπ f hfzero hflinear) (r : ℕ) (hr : 1 ≤ r) :
    FiniteLiftable π hπ f hfzero hflinear r hr := by
  obtain ⟨L⟩ := hL
  exact ⟨L.reduce π hπ f hfzero hflinear r hr⟩

omit hκ in
/-- A specified actual prime-residue equivalence identifies the cardinality
used in the lifting definition with the prime. -/
theorem residue_card_eq_prime (p : ℕ)
    (ε : IsLocalRing.ResidueField O ≃+* ZMod p) :
    Nat.card (IsLocalRing.ResidueField O) = p := by
  calc
    Nat.card (IsLocalRing.ResidueField O) = Nat.card (ZMod p) := Nat.card_congr ε.toEquiv
    _ = p := Nat.card_zmod p

section Numerical

variable (p e : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p]
  (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
  (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
  (τ δ : Γ) (hτlinear : (f τ).coeff 1 = 1)
  (ell : (IsLocalRing.ResidueField O)ˣ)
  (hell : (f δ).coeff 1 = (ell : IsLocalRing.ResidueField O))
  (horder : orderOf ell = p - 1)
  (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero (f τ) (hfzero τ)
    (hτlinear ▸ isUnit_one)))
  (hdiv : ∀ n : ℕ, (p : ℤ) ∣
    ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1).order - 1) + 1)
  (hfast : ∀ n : ℕ, ((p : ℤ) + 1) *
      ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1) ≤
    (HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ (n + 1))) -
      HahnSeries.single (1 : ℤ) 1).order - 1)
  (hlimit : Tendsto (fun n : ℕ ↦
    (((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
    (nhds (FalseTateExtension.kummerRamificationLimit p)))

include ε hu hpe hτlinear hell horder hinfinite hdiv hfast hlimit

/-- The actual numerical finite obstruction excludes full-family finite
lifts at `vπ(p)+1`; its stronger three-element producer is used directly. -/
theorem not_finiteLiftable_of_numerical_ramification :
    ¬ FiniteLiftable π hπ f hfzero hflinear (e + 1) (by omega) := by
  rintro ⟨L⟩
  have hP : mapRingHom (residue π hπ (e + 1) (by omega)) L.P =
      HahnSeries.single (p : ℤ) 1 := by
    simpa only [residue_card_eq_prime (O := O) p ε] using L.residue_P
  exact not_commuting_finite_lifts_of_numerical_ramification π hπ p e ε u hu hpe
    L.P hP (L.F τ) (L.F δ) (f τ) (f δ) (hfzero τ) hτlinear (hfzero δ)
    ell hell horder hinfinite (L.residue_F τ) (L.residue_F δ) hdiv hfast hlimit
    (L.commute τ) (L.commute δ)

/-- A completed lift would reduce to the forbidden actual finite lift.
The entire p-adic and differential argument is supplied by the checked
numerical finite producer, not by a caller-provided obstruction. -/
theorem not_liftable_of_numerical_ramification : ¬ Liftable π hπ f hfzero hflinear := by
  intro hL
  exact not_finiteLiftable_of_numerical_ramification π hπ f hfzero hflinear p e ε u hu hpe
    τ δ hτlinear ell hell horder hinfinite hdiv hfast hlimit
    (hL.finite π hπ f hfzero hflinear (e + 1) (by omega))

end Numerical

omit hκ

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
  [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F
local notation "O_0" => Valuation.valuationSubring (NormedField.valuation (K := Padic p))

/-- The numerical no-lift criterion for the actual spectral integers of a
finite totally ramified coefficient extension. The residue identification,
residue finiteness and characteristic, and the actual factorization of `p`
are constructed from the original coefficient field. -/
theorem coefficientExtension_not_liftable_of_numerical_ramification
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) (π : O_F) (hπ : Irreducible π)
    (f : Γ → PowerSeries (IsLocalRing.ResidueField O_F))
    (hfzero : ∀ g, (f g).constantCoeff = 0)
    (hflinear : ∀ g, IsUnit ((f g).coeff 1))
    (τ δ : Γ) (hτlinear : (f τ).coeff 1 = 1)
    (ell : (IsLocalRing.ResidueField O_F)ˣ)
    (hell : (f δ).coeff 1 = (ell : IsLocalRing.ResidueField O_F))
    (horder : orderOf ell = p - 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero (f τ) (hfzero τ)
      (hτlinear ▸ isUnit_one)))
    (hdiv : ∀ n : ℕ, (p : ℤ) ∣
      ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1) + 1)
    (hfast : ∀ n : ℕ, ((p : ℤ) + 1) *
        ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
          HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ (n + 1))) -
        HahnSeries.single (1 : ℤ) 1).order - 1)
    (hlimit : Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate (f τ) (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
      (nhds (FalseTateExtension.kummerRamificationLimit p))) :
    letI : Fintype (IsLocalRing.ResidueField O_F) := Fintype.ofEquiv (ZMod p)
      (coefficientExtensionPrimeResidueEquiv p F htotal).symm.toEquiv
    ¬ Liftable π hπ f hfzero hflinear := by
  let : Fintype (IsLocalRing.ResidueField O_F) := Fintype.ofEquiv (ZMod p)
    (coefficientExtensionPrimeResidueEquiv p F htotal).symm.toEquiv
  let : CharP (IsLocalRing.ResidueField O_F) p := coefficientExtensionResidue_charP p F htotal
  obtain ⟨e, u, hpe, -⟩ := coefficientExtension_exists_p_factor p F π hπ
  exact not_liftable_of_numerical_ramification π hπ f hfzero hflinear p e
    (coefficientExtensionPrimeResidueEquiv p F htotal) u u.isUnit hpe
    τ δ hτlinear ell hell horder hinfinite hdiv hfast hlimit

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing
