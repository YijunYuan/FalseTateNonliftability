module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Substitution on the actual completed coefficient ring

Positive-level substitutions commute with the actual coefficient factors.
Compatible coordinates are lifted into the same canonical `AdicCompletion`.
Uniqueness uses all prescribed positive coordinates.

This proves `nl:truncated-substitution-naturality`,
`nl:completed-coefficient-substitution`, and
`nl:completed-power-series-coordinate`.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O]

/-- The canonical equivalence identifying an ordinary completion coordinate
with Laurent series over the actual coefficient quotient. -/
def coordinateEquiv (π : O) (r : ℕ) :
    LaurentSeries O ⧸ (Ideal.span {(HahnSeries.C π : LaurentSeries O)}) ^ r ≃+*
      LaurentSeries (Truncation π r) :=
  (Ideal.quotEquivOfEq (span_C_pow π r)).trans (principalQuotientEquiv (π ^ r))

@[simp]
theorem coordinateEquiv_mk (π : O) (r : ℕ) (f : LaurentSeries O) :
    coordinateEquiv π r (Ideal.Quotient.mk _ f) = principalReduction (π ^ r) f := by
  simp only [coordinateEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    principalQuotientEquiv_mk]

/-- The coordinate equivalence uses the existing completion evaluation. -/
theorem coordinateEquiv_eval (π : O) (r : ℕ) (x : PrincipalCompletion π) :
    coordinateEquiv π r (AdicCompletion.evalₐ _ r x) = completedPrincipalReduction π r x := rfl

/-- The ordinary quotient factors correspond to actual coefficient factors. -/
theorem coordinateEquiv_factor (π : O) {s r : ℕ} (hsr : s ≤ r)
    (x : LaurentSeries O ⧸ (Ideal.span {(HahnSeries.C π : LaurentSeries O)}) ^ r) :
    mapRingHom (factor π hsr) (coordinateEquiv π r x) =
      coordinateEquiv π s (Ideal.Quotient.factorPow _ hsr x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change mapRingHom (factor π hsr) (coordinateEquiv π r (Ideal.Quotient.mk _ f)) =
    coordinateEquiv π s (Ideal.Quotient.mk _ f)
  simpa only [coordinateEquiv_mk] using factor_principalReduction π hsr f

/-- Actual Laurent coordinates jointly distinguish completion elements. -/
theorem completedPrincipalReduction_ext (π : O) {x y : PrincipalCompletion π}
    (h : ∀ r, completedPrincipalReduction π r x = completedPrincipalReduction π r y) : x = y := by
  apply AdicCompletion.ext_evalₐ
  intro r
  exact (coordinateEquiv π r).injective (h r)

/-- Positive coordinates suffice: the zeroth quotient is the zero ring. -/
theorem completedPrincipalReduction_ext_pos (π : O) {x y : PrincipalCompletion π}
    (h : ∀ r, 1 ≤ r → completedPrincipalReduction π r x = completedPrincipalReduction π r y) :
    x = y := by
  apply completedPrincipalReduction_ext π
  intro r
  by_cases hr : 1 ≤ r
  · exact h r hr
  · have hr0 : r = 0 := by omega
    subst r
    apply (coordinateEquiv π 0).symm.injective
    have htop : (Ideal.span {(HahnSeries.C π : LaurentSeries O)}) ^ 0 = ⊤ := by simp
    have : Subsingleton (LaurentSeries O ⧸ (Ideal.span {(HahnSeries.C π : LaurentSeries O)}) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    exact Subsingleton.elim _ _

/-- Compatibility transports through the canonical coefficient quotient equivalences. -/
theorem coordinateEquiv_compatible (π : O) {B : Type*} [CommRing B]
    (f : (r : ℕ) → B →+* LaurentSeries (Truncation π r))
    (hf : ∀ {s r} (hsr : s ≤ r),
      (mapRingHom (factor π hsr)).comp (f r) = f s) {s r} (hsr : s ≤ r) :
    (Ideal.Quotient.factorPow (Ideal.span {(HahnSeries.C π : LaurentSeries O)}) hsr).comp
        ((coordinateEquiv π r).symm.toRingHom.comp (f r)) =
      (coordinateEquiv π s).symm.toRingHom.comp (f s) := by
  ext x
  apply (coordinateEquiv π s).injective
  change coordinateEquiv π s (Ideal.Quotient.factorPow _ hsr
    ((coordinateEquiv π r).symm (f r x))) =
      coordinateEquiv π s ((coordinateEquiv π s).symm (f s x))
  rw [← coordinateEquiv_factor, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (hf hsr) x

/-- The canonical completion receives every compatible family of ring maps
to its actual Laurent coefficient quotients. -/
def liftCoordinates (π : O) {B : Type*} [CommRing B]
    (f : (r : ℕ) → B →+* LaurentSeries (Truncation π r))
    (hf : ∀ {s r} (hsr : s ≤ r),
      (mapRingHom (factor π hsr)).comp (f r) = f s) : B →+* PrincipalCompletion π :=
  AdicCompletion.liftRingHom _
    (fun r ↦ (coordinateEquiv π r).symm.toRingHom.comp (f r))
    (coordinateEquiv_compatible π f hf)

@[simp]
theorem completedPrincipalReduction_liftCoordinates (π : O) {B : Type*} [CommRing B]
    (f : (r : ℕ) → B →+* LaurentSeries (Truncation π r))
    (hf : ∀ {s r} (hsr : s ≤ r),
      (mapRingHom (factor π hsr)).comp (f r) = f s) (r : ℕ) (x : B) :
    completedPrincipalReduction π r (liftCoordinates π f hf x) = f r x := by
  rw [← coordinateEquiv_eval]
  exact (congrArg (coordinateEquiv π r)
    (AdicCompletion.evalₐ_liftRingHom _ _ (coordinateEquiv_compatible π f hf) r x)).trans
      ((coordinateEquiv π r).apply_symm_apply (f r x))

/-- The actual coordinates of an original coefficient are constant Laurent series. -/
@[simp]
theorem completedPrincipalReduction_scalar (π : O) (r : ℕ) (b : O) :
    completedPrincipalReduction π r (algebraMap O (PrincipalCompletion π) b) =
      HahnSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ r}) b) := by
  change completedPrincipalReduction π r
    (algebraMap (LaurentSeries O) (PrincipalCompletion π) (algebraMap O (LaurentSeries O) b)) = _
  rw [completedPrincipalReduction_algebraMap]
  simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C, principalReduction, mapRingHom_C]

/-- Canonical coefficient maps agree with ordinary power-series coefficient maps. -/
theorem mapRingHom_ofPowerSeries {S : Type*} [CommRing S] (ψ : O →+* S) (P : PowerSeries O) :
    mapRingHom ψ (HahnSeries.ofPowerSeries ℤ O P) =
      HahnSeries.ofPowerSeries ℤ S (PowerSeries.map ψ P) := by
  ext j
  simp only [mapRingHom_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp only [map_zero]

/-- The actual canonical image of power series in the principal completion. -/
def completedPowerSeries (π : O) : PowerSeries O →+* PrincipalCompletion π :=
  (algebraMap (LaurentSeries O) (PrincipalCompletion π)).comp (HahnSeries.ofPowerSeries ℤ O)

/-- The power-series image has the actual coefficientwise quotient coordinates. -/
@[simp]
theorem completedPrincipalReduction_powerSeries (π : O) (r : ℕ) (P : PowerSeries O) :
    completedPrincipalReduction π r (completedPowerSeries π P) =
      HahnSeries.ofPowerSeries ℤ (Truncation π r)
        (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π ^ r})) P) := by
  change completedPrincipalReduction π r
    (algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.ofPowerSeries ℤ O P)) = _
  rw [completedPrincipalReduction_algebraMap]
  exact mapRingHom_ofPowerSeries _ P

/-- Both actual inverse identities survive every coefficient ring map. -/
theorem map_powerSeries_inverse_identities {S : Type*} [CommRing S] (ψ : O →+* S)
    (P : PowerSeries O) (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1)) :
    (PowerSeries.map ψ P).subst (PowerSeries.map ψ (P.substInvOfIsUnit hlinear)) = PowerSeries.X ∧
      (PowerSeries.map ψ (P.substInvOfIsUnit hlinear)).subst (PowerSeries.map ψ P) =
        PowerSeries.X := by
  constructor
  · exact (PowerSeries.map_subst (h := ψ)
      (PowerSeries.HasSubst.substInvOfIsUnit P hlinear) P).symm.trans
        (by
          change PowerSeries.map ψ (P.subst (P.substInvOfIsUnit hlinear)) = PowerSeries.X
          rw [PowerSeries.subst_substInvOfIsUnit_right P hP hlinear, PowerSeries.map_X])
  · exact (PowerSeries.map_subst (h := ψ)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hP) (P.substInvOfIsUnit hlinear)).symm.trans
        (by
          change PowerSeries.map ψ ((P.substInvOfIsUnit hlinear).subst P) = PowerSeries.X
          rw [PowerSeries.subst_substInvOfIsUnit_left P hP hlinear, PowerSeries.map_X])

/-- Uniqueness of the actual inverse identifies its coefficientwise image. -/
theorem map_powerSeries_substInvOfIsUnit {S : Type*} [CommRing S] (ψ : O →+* S)
    (P : PowerSeries O) (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1)) :
    PowerSeries.map ψ (P.substInvOfIsUnit hlinear) =
      (PowerSeries.map ψ P).substInvOfIsUnit
        (by simpa only [PowerSeries.coeff_map] using hlinear.map ψ) := by
  apply PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _
    (by change ψ P.constantCoeff = 0; rw [hP, map_zero])
  · apply PowerSeries.HasSubst.of_constantCoeff_zero'
    change ψ (P.substInvOfIsUnit hlinear).constantCoeff = 0
    rw [PowerSeries.constantCoeff_substInvOfIsUnit, map_zero]
  · exact (map_powerSeries_inverse_identities ψ P hP hlinear).1

section DiscreteValuationRing

variable [IsDomain O] [IsDiscreteValuationRing O] (π : O) (hπ : Irreducible π)

/-- The existing canonical substitution on the actual positive coefficient quotient. -/
def truncatedSubst (r : ℕ) (hr : 1 ≤ r) (G : LaurentSeries (Truncation π r))
    (hG : IsAdmissible (parameter π r) G) :
    LaurentSeries (Truncation π r) →ₐ[Truncation π r] LaurentSeries (Truncation π r) := by
  letI := parameter_isMaximal π hπ r hr
  exact subst (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ G hG

@[simp]
theorem truncatedSubst_C (r : ℕ) (hr : 1 ≤ r) (G : LaurentSeries (Truncation π r))
    (hG : IsAdmissible (parameter π r) G) (b : Truncation π r) :
    truncatedSubst π hπ r hr G hG (HahnSeries.C b) = HahnSeries.C b := by
  simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C] using (truncatedSubst π hπ r hr G hG).commutes b

@[simp]
theorem truncatedSubst_X (r : ℕ) (hr : 1 ≤ r) (G : LaurentSeries (Truncation π r))
    (hG : IsAdmissible (parameter π r) G) :
    truncatedSubst π hπ r hr G hG (HahnSeries.single (1 : ℤ) 1) = G := by
  let := parameter_isMaximal π hπ r hr
  exact subst_X _ _ G hG

/-- Actual substitution commutes with every positive coefficient transition. -/
theorem factor_truncatedSubst {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : LaurentSeries (Truncation π r)) :
    mapRingHom (factor π hsr) (truncatedSubst π hπ r (hs.trans hsr) G hG f) =
      truncatedSubst π hπ s hs (mapRingHom (factor π hsr) G)
        ((isAdmissible_factor_iff π hπ hsr hs G).mpr hG) (mapRingHom (factor π hsr) f) := by
  let := parameter_isMaximal π hπ r (hs.trans hsr)
  let := parameter_isMaximal π hπ s hs
  obtain ⟨a, ha, horder⟩ := show ∃ a : ℤ, 0 < a ∧
    (principalReduction (parameter π r) G).orderTop = (a : WithTop ℤ) from hG
  obtain ⟨U, Y, c, _, hdecomp, hUorder, hUunit, hc, hY⟩ :=
    exists_nilpotentLaurentEval_data (parameter π r) G r (parameter_pow_eq_zero π r) a horder
  let q := factor π hsr
  let E := nilpotentLaurentEval (q (parameter π r)) (mapRingHom q U) (mapRingHom q Y)
    r (hs.trans hsr) (by simpa only [map_pow, map_zero] using congrArg q (parameter_pow_eq_zero π r)) a c ha hc
    (hUorder.ge.trans (orderTop_le_mapRingHom q U))
    (hY.trans (orderTop_le_mapRingHom q Y)) (hUunit.map (mapRingHom q))
  have hE : E = truncatedSubst π hπ s hs (mapRingHom q G)
      ((isAdmissible_factor_iff π hπ hsr hs G).mpr hG) := by
    apply subst_unique _ _ _ _ E (continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _)
    change E (HahnSeries.single (1 : ℤ) 1) = mapRingHom q G
    rw [nilpotentLaurentEval_X, hdecomp, map_add, map_mul, mapRingHom_C]
  have hsource : truncatedSubst π hπ r (hs.trans hsr) G hG =
      nilpotentLaurentEval (parameter π r) U Y r (hs.trans hsr)
        (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit :=
    subst_eq_nilpotentLaurentEval _ _ G hG (parameter π r) U Y r (hs.trans hsr)
      (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit hdecomp
  exact (congrArg (fun F : LaurentSeries (Truncation π r) →ₐ[Truncation π r]
    LaurentSeries (Truncation π r) ↦ mapRingHom q (F f)) hsource).trans
    ((mapRingHom_nilpotentLaurentEval q _ U Y r (hs.trans hsr)
    (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit f).trans
      (congrArg (fun F : LaurentSeries (Truncation π s) →ₐ[Truncation π s]
        LaurentSeries (Truncation π s) ↦ F (mapRingHom q f)) hE))

/-- The actual finite-level chain rule commutes with the same coefficient transitions. -/
theorem factor_truncatedSubst_derivative {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : LaurentSeries (Truncation π r)) :
    mapRingHom (factor π hsr)
        (derivative (Truncation π r) (truncatedSubst π hπ r (hs.trans hsr) G hG f)) =
      truncatedSubst π hπ s hs (mapRingHom (factor π hsr) G)
        ((isAdmissible_factor_iff π hπ hsr hs G).mpr hG)
        (derivative (Truncation π s) (mapRingHom (factor π hsr) f)) *
          derivative (Truncation π s) (mapRingHom (factor π hsr) G) := by
  let := parameter_isMaximal π hπ s hs
  exact (mapRingHom_derivative (factor π hsr) _).trans
    ((congrArg (derivative (Truncation π s))
      (factor_truncatedSubst π hπ hsr hs G hG f)).trans
        (derivative_subst _ _ _ _ _))

/-- The actual residue coordinate of the same principal completion. -/
def completedResidue : PrincipalCompletion π →+* LaurentSeries (IsLocalRing.ResidueField O) :=
  (mapRingHom (residue π hπ 1 le_rfl)).comp (completedPrincipalReduction π 1)

/-- Every positive coordinate has exactly this actual residue. -/
theorem completedResidue_eq (r : ℕ) (hr : 1 ≤ r) (G : PrincipalCompletion π) :
    completedResidue π hπ G =
      mapRingHom (residue π hπ r hr) (completedPrincipalReduction π r G) := by
  change mapRingHom (residue π hπ 1 le_rfl) (completedPrincipalReduction π 1 G) = _
  rw [← factor_completedPrincipalReduction π hr G, map_residue_factor]

/-- Admissibility means finite positive order of the actual residue Laurent series. -/
def CompletedIsAdmissible (G : PrincipalCompletion π) : Prop :=
  ∃ a : ℤ, 0 < a ∧ (completedResidue π hπ G).orderTop = (a : WithTop ℤ)

/-- Completed admissibility is precisely admissibility of every positive coordinate. -/
theorem completedIsAdmissible_iff (r : ℕ) (hr : 1 ≤ r) (G : PrincipalCompletion π) :
    CompletedIsAdmissible π hπ G ↔
      IsAdmissible (parameter π r) (completedPrincipalReduction π r G) := by
  rw [isAdmissible_iff_actualResidue π hπ r hr, CompletedIsAdmissible,
    completedResidue_eq π hπ r hr]

/-- The actual finite-level ring maps whose compatible lift defines substitution.
The zeroth coordinate is its unique possible map. -/
def substitutionCoordinate (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (r : ℕ) : PrincipalCompletion π →+* LaurentSeries (Truncation π r) :=
  if hr : 1 ≤ r then
    (truncatedSubst π hπ r hr (completedPrincipalReduction π r G)
      ((completedIsAdmissible_iff π hπ r hr G).mp hG)).toRingHom.comp
        (completedPrincipalReduction π r)
  else completedPrincipalReduction π r

/-- Positive-level naturality is the compatibility required by canonical completion. -/
theorem substitutionCoordinate_compatible (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) {s r : ℕ} (hsr : s ≤ r) :
    (mapRingHom (factor π hsr)).comp (substitutionCoordinate π hπ G hG r) =
      substitutionCoordinate π hπ G hG s := by
  ext f j
  by_cases hs : 1 ≤ s
  · have hr := hs.trans hsr
    simp only [substitutionCoordinate, dite_eq_left hs, dite_eq_left hr, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact congrArg (fun x : LaurentSeries (Truncation π s) ↦ x.coeff j)
      ((factor_truncatedSubst π hπ hsr hs _ _ _).trans (by
        simp only [factor_completedPrincipalReduction]))
  · have hs0 : s = 0 := by omega
    subst s
    have : Subsingleton (Truncation π 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp [Ideal.span_singleton_one])
    exact Subsingleton.elim _ _

/-- Actual substitution on the same canonical principal completion. -/
def completedSubst (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G) :
    PrincipalCompletion π →ₐ[O] PrincipalCompletion π where
  __ := liftCoordinates π (substitutionCoordinate π hπ G hG)
    (substitutionCoordinate_compatible π hπ G hG)
  commutes' b := by
    apply completedPrincipalReduction_ext_pos π
    intro r hr
    change completedPrincipalReduction π r (liftCoordinates π _ _
      (algebraMap O (PrincipalCompletion π) b)) = _
    rw [completedPrincipalReduction_liftCoordinates]
    simp only [substitutionCoordinate, dite_eq_left hr, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, completedPrincipalReduction_scalar,
      truncatedSubst_C]

/-- The prescribed actual positive coordinates of completed substitution. -/
@[simp]
theorem completedPrincipalReduction_completedSubst (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (r : ℕ) (hr : 1 ≤ r) (f : PrincipalCompletion π) :
    completedPrincipalReduction π r (completedSubst π hπ G hG f) =
      truncatedSubst π hπ r hr (completedPrincipalReduction π r G)
        ((completedIsAdmissible_iff π hπ r hr G).mp hG)
        (completedPrincipalReduction π r f) := by
  change completedPrincipalReduction π r (liftCoordinates π (substitutionCoordinate π hπ G hG)
    (substitutionCoordinate_compatible π hπ G hG) f) = _
  rw [completedPrincipalReduction_liftCoordinates]
  simp only [substitutionCoordinate, dite_eq_left hr, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- All prescribed positive coordinates determine the completed algebra homomorphism. -/
theorem completedSubst_unique (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (F : PrincipalCompletion π →ₐ[O] PrincipalCompletion π)
    (hF : ∀ r (hr : 1 ≤ r) f, completedPrincipalReduction π r (F f) =
      truncatedSubst π hπ r hr (completedPrincipalReduction π r G)
        ((completedIsAdmissible_iff π hπ r hr G).mp hG) (completedPrincipalReduction π r f)) :
    F = completedSubst π hπ G hG := by
  apply AlgHom.ext
  intro f
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  exact (hF r hr f).trans (completedPrincipalReduction_completedSubst π hπ G hG r hr f).symm

/-- The actual variable is sent to the actual completed parameter. -/
@[simp]
theorem completedSubst_X (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G) :
    completedSubst π hπ G hG (algebraMap (LaurentSeries O) (PrincipalCompletion π)
      (HahnSeries.single (1 : ℤ) 1)) = G := by
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  rw [completedPrincipalReduction_completedSubst π hπ G hG r hr,
    completedPrincipalReduction_algebraMap]
  simpa only [principalReduction, mapRingHom_single, map_one] using
    truncatedSubst_X π hπ r hr (completedPrincipalReduction π r G) _

/-- Admissibility is preserved by actual completed substitution. -/
theorem CompletedIsAdmissible.substitution {G H : PrincipalCompletion π}
    (hG : CompletedIsAdmissible π hπ G) (hH : CompletedIsAdmissible π hπ H) :
    CompletedIsAdmissible π hπ (completedSubst π hπ H hH G) := by
  rw [completedIsAdmissible_iff π hπ 1 le_rfl,
    completedPrincipalReduction_completedSubst π hπ H hH 1 le_rfl]
  let := parameter_isMaximal π hπ 1 le_rfl
  exact IsAdmissible.substitution _ _
    ((completedIsAdmissible_iff π hπ 1 le_rfl G).mp hG)
    ((completedIsAdmissible_iff π hπ 1 le_rfl H).mp hH)

/-- Composition is the actual substitution at the substituted completed parameter. -/
theorem completedSubst_comp (G H : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (hH : CompletedIsAdmissible π hπ H) :
    (completedSubst π hπ H hH).comp (completedSubst π hπ G hG) =
      completedSubst π hπ (completedSubst π hπ H hH G) (hG.substitution π hπ hH) := by
  apply AlgHom.ext
  intro f
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  let := parameter_isMaximal π hπ r hr
  simp only [AlgHom.comp_apply, completedPrincipalReduction_completedSubst π hπ _ _ r hr]
  exact subst_assoc _ _ _ _ _ _ _

/-- The named topology is the principal adic topology on the actual completion. -/
@[instance_reducible]
def completedAdicTopology : TopologicalSpace (PrincipalCompletion π) :=
  (Ideal.span {algebraMap O (PrincipalCompletion π) π}).adicTopology

/-- Completed substitution is continuous for the principal adic topology. -/
theorem continuous_completedSubst (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) :
    @Continuous _ _ (completedAdicTopology π) (completedAdicTopology π)
      (completedSubst π hπ G hG) := by
  let : WithIdeal (PrincipalCompletion π) := ⟨Ideal.span {algebraMap O (PrincipalCompletion π) π}⟩
  apply (WithIdeal.uniformContinuous_of_map_le
    (f := (completedSubst π hπ G hG).toRingHom) ?_).continuous
  change (Ideal.span {algebraMap O (PrincipalCompletion π) π}).map
    (completedSubst π hπ G hG).toRingHom ≤ Ideal.span {algebraMap O (PrincipalCompletion π) π}
  simp only [Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes]
  exact le_rfl

/-- A genuine zero-constant power-series coordinate with unit linear term
has admissible image in the actual completion. -/
theorem completedIsAdmissible_powerSeries (P : PowerSeries O) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) : CompletedIsAdmissible π hπ (completedPowerSeries π P) := by
  rw [completedIsAdmissible_iff π hπ 1 le_rfl, completedPrincipalReduction_powerSeries]
  let := parameter_isMaximal π hπ 1 le_rfl
  apply isAdmissible_ofPowerSeries
  · change Ideal.Quotient.mk _ P.constantCoeff = 0
    rw [hP, map_zero]
  · simpa only [PowerSeries.coeff_map] using hlinear.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))

/-- A power-series inverse identity gives the identity on the same completion,
by checking all actual positive coordinates. -/
theorem completedSubst_powerSeries_comp_eq_id (P Q : PowerSeries O)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0)
    (hPlinear : IsUnit (P.coeff 1)) (hQlinear : IsUnit (Q.coeff 1))
    (hQP : Q.subst P = PowerSeries.X) :
    (completedSubst π hπ (completedPowerSeries π P)
      (completedIsAdmissible_powerSeries π hπ P hP hPlinear)).comp
      (completedSubst π hπ (completedPowerSeries π Q)
        (completedIsAdmissible_powerSeries π hπ Q hQ hQlinear)) =
      AlgHom.id O (PrincipalCompletion π) := by
  apply AlgHom.ext
  intro f
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  let := parameter_isMaximal π hπ r hr
  let q := Ideal.Quotient.mk (Ideal.span {π ^ r})
  have hPQ : (PowerSeries.map q Q).subst (PowerSeries.map q P) = PowerSeries.X := by
    exact (PowerSeries.map_subst (h := q)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hP) Q).symm.trans
        (by
          change PowerSeries.map q (Q.subst P) = PowerSeries.X
          rw [hQP, PowerSeries.map_X])
  have hPr : (PowerSeries.map q P).constantCoeff = 0 := by
    change q P.constantCoeff = 0
    rw [hP, map_zero]
  have hQr : (PowerSeries.map q Q).constantCoeff = 0 := by
    change q Q.constantCoeff = 0
    rw [hQ, map_zero]
  have hPl : IsUnit ((PowerSeries.map q P).coeff 1) := by
    simpa only [PowerSeries.coeff_map] using hPlinear.map q
  have hQl : IsUnit ((PowerSeries.map q Q).coeff 1) := by
    simpa only [PowerSeries.coeff_map] using hQlinear.map q
  have heq := subst_ofPowerSeries_comp_eq_id (parameter π r)
    (show IsNilpotent (parameter π r) from ⟨r, parameter_pow_eq_zero π r⟩)
      (PowerSeries.map q P) (PowerSeries.map q Q) hPr hQr hPl hQl hPQ
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    completedPrincipalReduction_completedSubst π hπ _ _ r hr,
    completedPrincipalReduction_powerSeries]
  exact AlgHom.congr_fun heq (completedPrincipalReduction π r f)

/-- Actual completed substitutions at a power-series coordinate and its pinned
Mathlib inverse, packaged as an algebra automorphism. -/
def completedPowerSeriesSubstEquiv (P : PowerSeries O) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) : PrincipalCompletion π ≃ₐ[O] PrincipalCompletion π := by
  let Q := P.substInvOfIsUnit hlinear
  have hQ : Q.constantCoeff = 0 := PowerSeries.constantCoeff_substInvOfIsUnit P hlinear
  have hQlinear : IsUnit (Q.coeff 1) := by
    rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact Units.isUnit _
  exact AlgEquiv.ofAlgHom
    (completedSubst π hπ (completedPowerSeries π P)
      (completedIsAdmissible_powerSeries π hπ P hP hlinear))
    (completedSubst π hπ (completedPowerSeries π Q)
      (completedIsAdmissible_powerSeries π hπ Q hQ hQlinear))
    (completedSubst_powerSeries_comp_eq_id π hπ P Q hP hQ hlinear hQlinear
      (PowerSeries.subst_substInvOfIsUnit_left P hP hlinear))
    (completedSubst_powerSeries_comp_eq_id π hπ Q P hQ hP hQlinear hlinear
      (PowerSeries.subst_substInvOfIsUnit_right P hP hlinear))

@[simp]
theorem completedPowerSeriesSubstEquiv_apply (P : PowerSeries O) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : PrincipalCompletion π) :
    completedPowerSeriesSubstEquiv π hπ P hP hlinear f =
      completedSubst π hπ (completedPowerSeries π P)
        (completedIsAdmissible_powerSeries π hπ P hP hlinear) f := rfl

/-- The inverse automorphism is the actual substitution at the actual inverse coordinate. -/
theorem completedPowerSeriesSubstEquiv_symm_apply (P : PowerSeries O) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : PrincipalCompletion π) :
    (completedPowerSeriesSubstEquiv π hπ P hP hlinear).symm f =
      completedSubst π hπ (completedPowerSeries π (P.substInvOfIsUnit hlinear))
        (completedIsAdmissible_powerSeries π hπ _ (PowerSeries.constantCoeff_substInvOfIsUnit P hlinear)
          (by rw [PowerSeries.coeff_one_substInvOfIsUnit]; exact Units.isUnit _)) f := rfl

/-- The actual completed coordinate automorphism is adically continuous. -/
theorem continuous_completedPowerSeriesSubstEquiv (P : PowerSeries O) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) :
    @Continuous _ _ (completedAdicTopology π) (completedAdicTopology π)
      (completedPowerSeriesSubstEquiv π hπ P hP hlinear) :=
  continuous_completedSubst π hπ _ _

/-- Its actual inverse substitution is adically continuous. -/
theorem continuous_completedPowerSeriesSubstEquiv_symm (P : PowerSeries O)
    (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1)) :
    @Continuous _ _ (completedAdicTopology π) (completedAdicTopology π)
      (completedPowerSeriesSubstEquiv π hπ P hP hlinear).symm :=
  continuous_completedSubst π hπ _ _

/-- Each actual positive coordinate of the completed automorphism is exactly
the existing finite-level power-series substitution automorphism. -/
theorem completedPrincipalReduction_powerSeriesSubstEquiv (P : PowerSeries O)
    (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1))
    (r : ℕ) (hr : 1 ≤ r) (f : PrincipalCompletion π) :
    letI := parameter_isMaximal π hπ r hr
    completedPrincipalReduction π r (completedPowerSeriesSubstEquiv π hπ P hP hlinear f) =
      powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
        (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π ^ r})) P)
        (by change Ideal.Quotient.mk _ P.constantCoeff = 0; rw [hP, map_zero])
        (by simpa only [PowerSeries.coeff_map] using
          hlinear.map (Ideal.Quotient.mk (Ideal.span {π ^ r})))
        (completedPrincipalReduction π r f) := by
  let := parameter_isMaximal π hπ r hr
  simp only [completedPowerSeriesSubstEquiv_apply,
    completedPrincipalReduction_completedSubst π hπ _ _ r hr,
    completedPrincipalReduction_powerSeries]
  rfl

/-- The inverse coordinate is the canonical inverse at each positive level;
coefficientwise transport of the actual two-sided inverse is used explicitly. -/
theorem completedPrincipalReduction_powerSeriesSubstEquiv_symm (P : PowerSeries O)
    (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1))
    (r : ℕ) (hr : 1 ≤ r) (f : PrincipalCompletion π) :
    letI := parameter_isMaximal π hπ r hr
    completedPrincipalReduction π r ((completedPowerSeriesSubstEquiv π hπ P hP hlinear).symm f) =
      (powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
        (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π ^ r})) P)
        (by change Ideal.Quotient.mk _ P.constantCoeff = 0; rw [hP, map_zero])
        (by simpa only [PowerSeries.coeff_map] using
          hlinear.map (Ideal.Quotient.mk (Ideal.span {π ^ r})))).symm
        (completedPrincipalReduction π r f) := by
  let := parameter_isMaximal π hπ r hr
  simp only [completedPowerSeriesSubstEquiv_symm_apply,
    completedPrincipalReduction_completedSubst π hπ _ _ r hr,
    completedPrincipalReduction_powerSeries,
    map_powerSeries_substInvOfIsUnit _ P hP hlinear]
  rfl

end DiscreteValuationRing

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
  [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F

/-- Completed substitution for the actual spectral integer ring of a finite
coefficient extension, with an actual uniformizer of that same ring. -/
abbrev coefficientExtensionSubst (π : O_F) (hπ : Irreducible π)
    (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G) :
    PrincipalCompletion π →ₐ[O_F] PrincipalCompletion π := completedSubst π hπ G hG

/-- The finite coefficient-extension substitution uses the same actual coordinates. -/
theorem coefficientExtensionSubst_coordinate (π : O_F) (hπ : Irreducible π)
    (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (r : ℕ) (hr : 1 ≤ r) (f : PrincipalCompletion π) :
    completedPrincipalReduction π r (coefficientExtensionSubst p F π hπ G hG f) =
      truncatedSubst π hπ r hr (completedPrincipalReduction π r G)
        ((completedIsAdmissible_iff π hπ r hr G).mp hG) (completedPrincipalReduction π r f) :=
  completedPrincipalReduction_completedSubst π hπ G hG r hr f

/-- Actual power-series coordinate automorphisms over the spectral integer ring. -/
abbrev coefficientExtensionPowerSeriesSubstEquiv (π : O_F) (hπ : Irreducible π)
    (P : PowerSeries O_F) (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1)) :
    PrincipalCompletion π ≃ₐ[O_F] PrincipalCompletion π :=
  completedPowerSeriesSubstEquiv π hπ P hP hlinear

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing
