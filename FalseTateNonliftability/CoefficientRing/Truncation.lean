module

public import FalseTateNonliftability.CoefficientRing.Quotient
public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateExtension.Padic.CyclotomicRamification
public import FontaineWintenberger.LocalField.FiniteExtension

/-!
# Actual truncated coefficient rings and their residue field

All coefficient rings are the canonical quotients `O / (π ^ r)`. Their
factor maps include level zero; residue maps and their actual residue-field
equivalences require positive levels. These maps agree coefficientwise with
the coordinates of the existing principal Laurent completion.

This proves blueprint lemmas `nl:positive-coefficient-truncations` and
`nl:coefficient-extension-truncations`.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O]

/-- The actual coefficient quotient; this abbreviation introduces no new carrier. -/
abbrev Truncation (π : O) (r : ℕ) := O ⧸ Ideal.span {π ^ r}

/-- The actual image of the chosen uniformizer in its coefficient quotient. -/
def parameter (π : O) (r : ℕ) : Truncation π r := Ideal.Quotient.mk _ π

/-- The defining quotient relation, including the zero ring at level zero. -/
theorem parameter_pow_eq_zero (π : O) (r : ℕ) : parameter π r ^ r = 0 := by
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Principal powers decrease with the exponent. -/
theorem span_pow_le (π : O) {s r : ℕ} (hsr : s ≤ r) :
    Ideal.span ({π ^ r} : Set O) ≤ Ideal.span {π ^ s} := by
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right hsr

/-- The actual quotient factor map, defined at every level including zero. -/
def factor (π : O) {s r : ℕ} (hsr : s ≤ r) : Truncation π r →+* Truncation π s :=
  Ideal.Quotient.factor (span_pow_le π hsr)

@[simp]
theorem factor_mk (π : O) {s r : ℕ} (hsr : s ≤ r) (x : O) :
    factor π hsr (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

@[simp]
theorem factor_parameter (π : O) {s r : ℕ} (hsr : s ≤ r) :
    factor π hsr (parameter π r) = parameter π s := rfl

/-- Quotient transition maps are surjective without a positivity restriction. -/
theorem factor_surjective (π : O) {s r : ℕ} (hsr : s ≤ r) :
    Function.Surjective (factor π hsr) := Ideal.Quotient.factor_surjective _

@[simp]
theorem factor_self (π : O) (r : ℕ) : factor π (le_refl r) = RingHom.id _ :=
  Ideal.Quotient.factor_eq

@[simp]
theorem factor_comp (π : O) {t s r : ℕ} (hts : t ≤ s) (hsr : s ≤ r) :
    (factor π hts).comp (factor π hsr) = factor π (hts.trans hsr) :=
  Ideal.Quotient.factor_comp _ _

/-- The coefficientwise identity transition is the identity on the actual Laurent carrier. -/
theorem map_factor_self (π : O) (r : ℕ) (G : LaurentSeries (Truncation π r)) :
    mapRingHom (factor π (le_refl r)) G = G := by
  ext j
  simp only [mapRingHom_coeff, factor_self, RingHom.id_apply]

/-- Coefficientwise transition maps compose in the same tower. -/
theorem map_factor_comp (π : O) {t s r : ℕ} (hts : t ≤ s) (hsr : s ≤ r)
    (G : LaurentSeries (Truncation π r)) :
    mapRingHom (factor π hts) (mapRingHom (factor π hsr) G) =
      mapRingHom (factor π (hts.trans hsr)) G := by
  ext j
  exact RingHom.congr_fun (factor_comp π hts hsr) (G.coeff j)

/-- Coefficient transitions agree with ordinary principal Laurent reduction. -/
theorem factor_principalReduction (π : O) {s r : ℕ} (hsr : s ≤ r) (f : LaurentSeries O) :
    mapRingHom (factor π hsr) (principalReduction (π ^ r) f) = principalReduction (π ^ s) f := by
  ext j
  simp only [mapRingHom_coeff, principalReduction_coeff, factor_mk]

/-- The existing principal-completion coordinates are compatible with every
coefficient transition, including the level-zero coordinate. -/
theorem factor_completedPrincipalReduction (π : O) {s r : ℕ} (hsr : s ≤ r)
    (x : PrincipalCompletion π) :
    mapRingHom (factor π hsr) (completedPrincipalReduction π r x) =
      completedPrincipalReduction π s x := by
  obtain ⟨f, hf⟩ := principalReduction_surjective (π ^ r) (completedPrincipalReduction π r x)
  have hker : RingHom.ker (completedPrincipalReduction π r) ≤
      RingHom.ker (completedPrincipalReduction π s) := by
    rw [ker_completedPrincipalReduction, ker_completedPrincipalReduction]
    exact span_pow_le _ hsr
  have hrzero : completedPrincipalReduction π r
      (x - algebraMap (LaurentSeries O) (PrincipalCompletion π) f) = 0 := by
    rw [map_sub, completedPrincipalReduction_algebraMap, hf, sub_self]
  have hszero := hker hrzero
  have hs : completedPrincipalReduction π s x = principalReduction (π ^ s) f := by
    apply sub_eq_zero.mp
    simpa only [RingHom.mem_ker, map_sub, completedPrincipalReduction_algebraMap] using hszero
  rw [← hf, factor_principalReduction, hs]

section DiscreteValuationRing

variable [IsDomain O] [IsDiscreteValuationRing O] (π : O) (hπ : Irreducible π)

include hπ

/-- The maximal ideal maps to the ideal of the actual uniformizer image. -/
theorem maximalIdeal_map (r : ℕ) :
    (IsLocalRing.maximalIdeal O).map (Ideal.Quotient.mk (Ideal.span {π ^ r})) =
      Ideal.span {parameter π r} := by
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- Only positive truncation ideals lie in the original maximal ideal. -/
theorem span_pow_le_maximalIdeal (r : ℕ) (hr : 1 ≤ r) :
    Ideal.span ({π ^ r} : Set O) ≤ IsLocalRing.maximalIdeal O := by
  rw [hπ.maximalIdeal_eq]
  simpa only [pow_one] using span_pow_le π hr

/-- The distinguished nilpotent generates a maximal ideal at each positive level. -/
theorem parameter_isMaximal (r : ℕ) (hr : 1 ≤ r) :
    (Ideal.span ({parameter π r} : Set (Truncation π r))).IsMaximal := by
  rw [← maximalIdeal_map π hπ r]
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact span_pow_le_maximalIdeal π hπ r hr

/-- The actual original residue map factored through a positive coefficient quotient. -/
def residue (r : ℕ) (hr : 1 ≤ r) : Truncation π r →+* IsLocalRing.ResidueField O :=
  Ideal.Quotient.factor (span_pow_le_maximalIdeal π hπ r hr)

@[simp]
theorem residue_mk (r : ℕ) (hr : 1 ≤ r) (x : O) :
    residue π hπ r hr (Ideal.Quotient.mk _ x) = IsLocalRing.residue O x := rfl

/-- This is the actual residue-field surjection. -/
theorem residue_surjective (r : ℕ) (hr : 1 ≤ r) :
    Function.Surjective (residue π hπ r hr) := Ideal.Quotient.factor_surjective _

/-- Its kernel is the actual principal nilpotent ideal. -/
theorem ker_residue (r : ℕ) (hr : 1 ≤ r) :
    RingHom.ker (residue π hπ r hr) = Ideal.span {parameter π r} := by
  change RingHom.ker (Ideal.Quotient.factor (span_pow_le_maximalIdeal π hπ r hr)) = _
  exact (Ideal.Quotient.factor_ker _).trans (maximalIdeal_map π hπ r)

/-- The canonical third-isomorphism equivalence with the actual residue field of `O`. -/
def residueEquiv (r : ℕ) (hr : 1 ≤ r) :
    Truncation π r ⧸ Ideal.span {parameter π r} ≃+* IsLocalRing.ResidueField O :=
  (Ideal.quotEquivOfEq (maximalIdeal_map π hπ r).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (span_pow_le_maximalIdeal π hπ r hr))

@[simp]
theorem residueEquiv_mk_mk (r : ℕ) (hr : 1 ≤ r) (x : O) :
    residueEquiv π hπ r hr (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      IsLocalRing.residue O x := rfl

@[simp]
theorem residueEquiv_mk (r : ℕ) (hr : 1 ≤ r) (x : Truncation π r) :
    residueEquiv π hπ r hr (Ideal.Quotient.mk _ x) = residue π hπ r hr x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Positive-level transition maps commute with the same original residue field. -/
theorem residue_factor {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s) :
    (residue π hπ s hs).comp (factor π hsr) = residue π hπ r (hs.trans hsr) := by
  ext x
  rfl

/-- The residue equivalence identifies actual principal Laurent reduction
with coefficientwise application of the original residue map. -/
theorem map_residueEquiv_principalReduction (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) :
    mapRingHom (residueEquiv π hπ r hr).toRingHom (principalReduction (parameter π r) G) =
      mapRingHom (residue π hπ r hr) G := by
  ext j
  simp only [mapRingHom_coeff, principalReduction_coeff]
  exact residueEquiv_mk π hπ r hr (G.coeff j)

/-- Actual residue Laurent series agree after every positive-level transition. -/
theorem map_residue_factor {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (G : LaurentSeries (Truncation π r)) :
    mapRingHom (residue π hπ s hs) (mapRingHom (factor π hsr) G) =
      mapRingHom (residue π hπ r (hs.trans hsr)) G := by
  ext j
  exact RingHom.congr_fun (residue_factor π hπ hsr hs) (G.coeff j)

/-- Admissibility uses finite positive order in the same actual residue Laurent field. -/
theorem isAdmissible_iff_actualResidue (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) :
    IsAdmissible (parameter π r) G ↔ ∃ a : ℤ, 0 < a ∧
      (mapRingHom (residue π hπ r hr) G).orderTop = (a : WithTop ℤ) := by
  have horder : (mapRingHom (residue π hπ r hr) G).orderTop =
      (principalReduction (parameter π r) G).orderTop := by
    rw [← map_residueEquiv_principalReduction π hπ r hr G]
    exact orderTop_mapRingHom_of_injective (residueEquiv π hπ r hr).toRingHom
      (residueEquiv π hπ r hr).injective _
  simp only [IsAdmissible, horder]

/-- Positive-level factors preserve and reflect actual admissibility. -/
theorem isAdmissible_factor_iff {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (G : LaurentSeries (Truncation π r)) :
    IsAdmissible (parameter π s) (mapRingHom (factor π hsr) G) ↔
      IsAdmissible (parameter π r) G := by
  rw [isAdmissible_iff_actualResidue π hπ s hs,
    isAdmissible_iff_actualResidue π hπ r (hs.trans hsr), map_residue_factor π hπ hsr hs]

end DiscreteValuationRing

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra (Padic p) F]
  [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F

/-- The parameter of an actual finite coefficient extension is the image of its
chosen uniformizer, with its actual truncation nilpotence relation. -/
theorem coefficientExtension_parameter_pow_eq_zero (π : O_F) (r : ℕ) : parameter π r ^ r = 0 :=
  parameter_pow_eq_zero π r

/-- The existing spectral-integer DVR instance supplies maximality in every
positive actual coefficient truncation. No new norm on `F` is chosen. -/
theorem coefficientExtension_parameter_isMaximal (π : O_F) (hπ : Irreducible π)
    (r : ℕ) (hr : 1 ≤ r) :
    (Ideal.span ({parameter π r} : Set (Truncation π r))).IsMaximal :=
  parameter_isMaximal π hπ r hr

/-- The residue equivalence for the actual spectral integers of the finite
extension, with their original residue-field object. -/
def coefficientExtensionResidueEquiv (π : O_F) (hπ : Irreducible π) (r : ℕ) (hr : 1 ≤ r) :
    Truncation π r ⧸ Ideal.span {parameter π r} ≃+* IsLocalRing.ResidueField O_F :=
  residueEquiv π hπ r hr

@[simp]
theorem coefficientExtensionResidueEquiv_mk_mk (π : O_F) (hπ : Irreducible π)
    (r : ℕ) (hr : 1 ≤ r) (x : O_F) :
    coefficientExtensionResidueEquiv p F π hπ r hr
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = IsLocalRing.residue O_F x := rfl

/-- The existing canonical substitution predicate is detected in the actual
residue Laurent field of the finite coefficient extension. -/
theorem coefficientExtension_isAdmissible_iff_actualResidue (π : O_F) (hπ : Irreducible π)
    (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) :
    IsAdmissible (parameter π r) G ↔ ∃ a : ℤ, 0 < a ∧
      (mapRingHom (residue π hπ r hr) G).orderTop = (a : WithTop ℤ) :=
  isAdmissible_iff_actualResidue π hπ r hr G

/-- The actual principal completion of the spectral integer Laurent ring has
the same compatible coordinates, including level zero. -/
theorem coefficientExtension_factor_completedPrincipalReduction (π : O_F)
    {s r : ℕ} (hsr : s ≤ r)
    (x : PrincipalCompletion π) :
    mapRingHom (factor π hsr) (completedPrincipalReduction π r x) =
      completedPrincipalReduction π s x :=
  factor_completedPrincipalReduction π hsr x

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing

end
