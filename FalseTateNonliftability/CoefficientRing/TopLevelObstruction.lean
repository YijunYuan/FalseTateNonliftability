/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.CoordinateChange
public import FalseTateNonliftability.CoefficientRing.ValuationBound
public import FalseTateNonliftability.LaurentSeries.IterateGrowth

/-!
# A numerical criterion excluding the top derivative level

Actual iterates of a commuting finite coefficient substitution remain
commuting and have their original residue iterates. Normal forms and actual
coordinate lifts then exclude the top normalized derivative level under
explicit congruence and growth conditions on the residue ramification numbers.

This proves the generic `nl:top-level-obstruction-criterion`, adapting Yuan,
Section 6. The actual false Tate action and its ramification profile are
separate inputs to its later application.
-/

@[expose] public section

noncomputable section

open Filter

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (π : O) (hπ : Irreducible π)

/-- The original finite substitution iterated on the actual variable. -/
def truncatedSubstIterate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G) (n : ℕ) :
    LaurentSeries (Truncation π r) :=
  (truncatedSubst π hπ r hr G hG)^[n] (HahnSeries.single (1 : ℤ) 1)

@[simp]
theorem truncatedSubstIterate_zero (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G) :
    truncatedSubstIterate π hπ r hr G hG 0 = HahnSeries.single (1 : ℤ) 1 := rfl

theorem truncatedSubstIterate_succ (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G) (n : ℕ) :
    truncatedSubstIterate π hπ r hr G hG (n + 1) =
      truncatedSubst π hπ r hr G hG (truncatedSubstIterate π hπ r hr G hG n) := by
  simp only [truncatedSubstIterate, Function.iterate_succ_apply']

/-- Every actual finite iterate remains an admissible original parameter. -/
theorem isAdmissible_truncatedSubstIterate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G) (n : ℕ) :
    IsAdmissible (parameter π r) (truncatedSubstIterate π hπ r hr G hG n) := by
  let := parameter_isMaximal π hπ r hr
  induction n with
  | zero =>
    simpa only [truncatedSubstIterate_zero, HahnSeries.ofPowerSeries_X] using
      isAdmissible_ofPowerSeries (parameter π r) (PowerSeries.X : PowerSeries (Truncation π r))
        (by simp) (by simp)
  | succ n ih =>
    rw [truncatedSubstIterate_succ]
    exact ih.substitution (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ hG

/-- Substitution at the actual iterated parameter is the original iterated
homomorphism on every Laurent input. -/
theorem truncatedSubst_truncatedSubstIterate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (n : ℕ) (x : LaurentSeries (Truncation π r)) :
    truncatedSubst π hπ r hr (truncatedSubstIterate π hπ r hr G hG n)
      (isAdmissible_truncatedSubstIterate π hπ r hr G hG n) x =
      (truncatedSubst π hπ r hr G hG)^[n] x := by
  let := parameter_isMaximal π hπ r hr
  let := orderTopology (Truncation π r)
  have := orderTopology_t2Space (R := Truncation π r)
  induction n with
  | zero =>
    have hid := subst_unique (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
      (HahnSeries.single (1 : ℤ) 1)
      (isAdmissible_truncatedSubstIterate π hπ r hr G hG 0)
      (AlgHom.id (Truncation π r) (LaurentSeries (Truncation π r))) continuous_id rfl
    exact (AlgHom.congr_fun hid x).symm
  | succ n ih =>
    have heq := subst_unique (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
      (truncatedSubstIterate π hπ r hr G hG (n + 1))
      (isAdmissible_truncatedSubstIterate π hπ r hr G hG (n + 1))
      ((truncatedSubst π hπ r hr G hG).comp
        (truncatedSubst π hπ r hr (truncatedSubstIterate π hπ r hr G hG n)
          (isAdmissible_truncatedSubstIterate π hπ r hr G hG n)))
      ((continuous_subst _ _ _ _).comp (continuous_subst _ _ _ _))
      (by
        simp only [AlgHom.comp_apply, truncatedSubst_X]
        exact (truncatedSubstIterate_succ π hπ r hr G hG n).symm)
    have h := AlgHom.congr_fun heq x
    change truncatedSubst π hπ r hr G hG
      (truncatedSubst π hπ r hr (truncatedSubstIterate π hπ r hr G hG n)
        (isAdmissible_truncatedSubstIterate π hπ r hr G hG n) x) =
      truncatedSubst π hπ r hr (truncatedSubstIterate π hπ r hr G hG (n + 1))
        (isAdmissible_truncatedSubstIterate π hπ r hr G hG (n + 1)) x at h
    rw [← h, ih, Function.iterate_succ_apply']

local instance topLevelZeroSpanIsMaximal {k : Type*} [Field k] :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- A genuine residue power-series coordinate supplies finite admissibility. -/
theorem isAdmissible_of_residue_powerSeries (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r))
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hlinear : IsUnit (f.coeff 1))
    (hres : mapRingHom (residue π hπ r hr) G = HahnSeries.ofPowerSeries ℤ _ f) :
    IsAdmissible (parameter π r) G := by
  rw [isAdmissible_iff_actualResidue π hπ r hr, hres]
  exact (isAdmissible_zero_iff _).mp (isAdmissible_ofPowerSeries 0 f hf hlinear)

/-- The residue substitution at an actual power-series residue is the
canonical power-series coordinate automorphism on the original residue field. -/
theorem residue_substitution_eq_powerSeriesSubstEquiv (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hlinear : IsUnit (f.coeff 1))
    (hres : mapRingHom (residue π hπ r hr) G = HahnSeries.ofPowerSeries ℤ _ f) :
    subst 0 IsNilpotent.zero (mapRingHom (residue π hπ r hr) G)
        (isAdmissible_residue π hπ r hr G hG) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hlinear).toAlgHom := by
  symm
  apply subst_unique
  · exact continuous_powerSeriesSubstEquiv _ _ _ _ _
  · simpa only [AlgEquiv.coe_toAlgHom, powerSeriesSubstEquiv_apply, subst_X] using hres.symm

/-- Reduction of the original finite iterate is exactly the original
power-series iterate, rather than an independently chosen lift. -/
theorem residue_truncatedSubstIterate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hlinear : IsUnit (f.coeff 1))
    (hres : mapRingHom (residue π hπ r hr) G = HahnSeries.ofPowerSeries ℤ _ f) (n : ℕ) :
    mapRingHom (residue π hπ r hr) (truncatedSubstIterate π hπ r hr G hG n) =
      HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f n) := by
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hlinear
  have heq := (residue_substitution_eq_powerSeriesSubstEquiv π hπ r hr G hG f hf hlinear hres).symm
  have hsemi : Function.Semiconj (mapRingHom (residue π hπ r hr))
      (truncatedSubst π hπ r hr G hG) E := by
    intro x
    rw [residue_truncatedSubst]
    exact (AlgHom.congr_fun heq _).symm
  calc
    _ = E^[n] (mapRingHom (residue π hπ r hr) (HahnSeries.single (1 : ℤ) 1)) :=
      hsemi.iterate_right n _
    _ = E^[n] (HahnSeries.single (1 : ℤ) 1) := by rw [mapRingHom_single, map_one]
    _ = _ := (ofPowerSeries_powerSeriesIterate f hf hlinear n).symm

/-- Equality of the actual commuting parameters gives commutation on every
Laurent input, by continuity and canonical substitution uniqueness. -/
theorem truncatedSubst_commute (r : ℕ) (hr : 1 ≤ r)
    (P G : LaurentSeries (Truncation π r))
    (hP : IsAdmissible (parameter π r) P) (hG : IsAdmissible (parameter π r) G)
    (hcomm : truncatedSubst π hπ r hr P hP G = truncatedSubst π hπ r hr G hG P) :
    Function.Commute (truncatedSubst π hπ r hr P hP) (truncatedSubst π hπ r hr G hG) := by
  let := parameter_isMaximal π hπ r hr
  let := orderTopology (Truncation π r)
  have := orderTopology_t2Space (R := Truncation π r)
  have heq : (truncatedSubst π hπ r hr P hP).comp (truncatedSubst π hπ r hr G hG) =
      (truncatedSubst π hπ r hr G hG).comp (truncatedSubst π hπ r hr P hP) := by
    apply continuous_algHom_ext_X
    · exact (continuous_subst _ _ _ _).comp (continuous_subst _ _ _ _)
    · exact (continuous_subst _ _ _ _).comp (continuous_subst _ _ _ _)
    · simpa only [AlgHom.comp_apply, truncatedSubst_X] using hcomm
  exact fun x ↦ AlgHom.congr_fun heq x

/-- Every actual finite iterate of a commuting parameter still commutes;
this is derived from the original identity, never an extra iterate hypothesis. -/
theorem truncatedSubstIterate_commute (r : ℕ) (hr : 1 ≤ r)
    (P G : LaurentSeries (Truncation π r))
    (hP : IsAdmissible (parameter π r) P) (hG : IsAdmissible (parameter π r) G)
    (hcomm : truncatedSubst π hπ r hr P hP G = truncatedSubst π hπ r hr G hG P) (n : ℕ) :
    truncatedSubst π hπ r hr P hP (truncatedSubstIterate π hπ r hr G hG n) =
      truncatedSubst π hπ r hr (truncatedSubstIterate π hπ r hr G hG n)
        (isAdmissible_truncatedSubstIterate π hπ r hr G hG n) P := by
  rw [truncatedSubst_truncatedSubstIterate]
  have h := (truncatedSubst_commute π hπ r hr P G hP hG hcomm).iterate_right n
  simpa only [truncatedSubstIterate, truncatedSubst_X] using h (HahnSeries.single (1 : ℤ) 1)

private theorem exists_primePowerIterate_normalForm {k : Type*} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one))) (n : ℕ)
    (hdiv : (p : ℤ) ∣ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1).order)
    (hfast : ((p : ℤ) + 1) *
        ((HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ (n + 1))) - HahnSeries.single (1 : ℤ) 1).order - 1) :
    let d := (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1
    ∃ (w : PowerSeries k) (_hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1)) (α : k),
      α ≠ 0 ∧ HahnSeries.ofPowerSeries ℤ k (powerSeriesConjugate (powerSeriesIterate f (p ^ n)) w hwlinear) -
        HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1) := by
  let g := powerSeriesIterate f (p ^ n)
  let δ := HahnSeries.ofPowerSeries ℤ k g - HahnSeries.single (1 : ℤ) 1
  let d := δ.order - 1
  have hg0 : g.constantCoeff = 0 := (powerSeriesIterate_spec f hf _).1
  have hg1 : g.coeff 1 = 1 := by rw [(powerSeriesIterate_spec f hf _).2, hlinear, one_pow]
  have hglinear : IsUnit (g.coeff 1) := by rw [hg1]; exact isUnit_one
  have hδ : δ ≠ 0 := powerSeriesIterate_displacement_ne_zero f hf _ hinfinite _
    (pow_pos (Fact.out : p.Prime).pos n)
  have hd : 1 ≤ d := by
    have h := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite _
      (pow_pos (Fact.out : p.Prime).pos n)
    change 2 ≤ δ.order at h
    dsimp only [d]
    omega
  have hfinite : δ.orderTop = ((d + 1 : ℤ) : WithTop ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hδ]
    congr 1
    dsimp only [d]
    omega
  have hdp : (p : ℤ) ∣ d + 1 := by simpa only [d, sub_add_cancel] using hdiv
  have hnext : (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0 hglinear)^[p]
      (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup (((p : ℤ) + 1) * d + 1) := by
    have hi : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0 hglinear =
        (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
          (by rw [hlinear]; exact isUnit_one)) ^ (p ^ n) :=
      powerSeriesSubstEquiv_powerSeriesIterate f hf _ (p ^ n)
    have he : (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg0 hglinear)^[p]
        (HahnSeries.single (1 : ℤ) 1) =
        HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ (n + 1))) := by
      rw [← AlgEquiv.coe_pow, hi, ← pow_mul, ← pow_succ]
      simpa only [AlgEquiv.coe_pow] using
        (ofPowerSeries_powerSeriesIterate f hf (by rw [hlinear]; exact isUnit_one) (p ^ (n + 1))).symm
    rw [he]
    have hne := powerSeriesIterate_displacement_ne_zero f hf _ hinfinite _
      (pow_pos (Fact.out : p.Prime).pos (n + 1))
    change ((((p : ℤ) + 1) * d + 1 : ℤ) : WithTop ℤ) ≤ _
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne]
    apply WithTop.coe_le_coe.mpr
    change ((p : ℤ) + 1) * d ≤ _ - 1 at hfast
    omega
  exact exists_powerSeries_normalForm p g hg0 hglinear d hd hdp hfinite hnext

private theorem residue_coordinateConjugate_ofPowerSeries (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hlinear : IsUnit (f.coeff 1))
    (hres : mapRingHom (residue π hπ r hr) G = HahnSeries.ofPowerSeries ℤ _ f)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hHlinear : IsUnit (H.coeff 1)) :
    mapRingHom (residue π hπ r hr) (coordinateConjugate π hπ r hr G hG H hzero hHlinear) =
      HahnSeries.ofPowerSeries ℤ _ (powerSeriesConjugate f (H.map (residue π hπ r hr))
        (by simpa only [PowerSeries.coeff_map] using hHlinear.map (residue π hπ r hr))) := by
  rw [residue_coordinateConjugate_apply,
    ofPowerSeries_powerSeriesConjugate f _ hf hlinear
      (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using hHlinear.map (residue π hπ r hr))]
  congr 1
  exact AlgHom.congr_fun
    (residue_substitution_eq_powerSeriesSubstEquiv π hπ r hr G hG f hf hlinear hres) _

/-- **The numerical top-level obstruction criterion.** The actual finite
Frobenius lift cannot have top derivative level if it commutes with a lift
whose actual residue iterates satisfy the displayed congruence and growth.
Normal forms, lifted coordinates and iterated commutation are all constructed. -/
theorem derivativeLevel_lt_of_iterate_growth (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (G : LaurentSeries (Truncation π (e + 1)))
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (hres : mapRingHom (residue π hπ (e + 1) (by omega)) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hdiv : ∀ n : ℕ, (p : ℤ) ∣
      ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1) + 1)
    (hfast : ∀ n : ℕ, ((p : ℤ) + 1) *
        ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ (n + 1))) - HahnSeries.single (1 : ℤ) 1).order - 1)
    (hcomm : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G
        (isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) G f hf
          (by rw [hlinear]; exact isUnit_one) hres) P) :
    derivativeLevel π hπ p e u hu hpe P hP < e := by
  by_contra hnot
  have hs : derivativeLevel π hπ p e u hu hpe P hP = e := by
    have h := (derivativeLevel_spec π hπ p e u hu hpe P hP).2.1
    omega
  let m := (normalizedDerivative π hπ p e u hu hpe P hP).order
  have ht := tendsto_primePowerIterate_ramification_atTop p f hf hlinear hinfinite
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 ht ((p : ℤ) - m)).exists
  let d := (HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) - HahnSeries.single (1 : ℤ) 1).order - 1
  change (p : ℤ) - m ≤ d at hn
  have hd : 1 ≤ d := by
    have h := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite _
      (pow_pos (Fact.out : p.Prime).pos n)
    dsimp only [d]
    omega
  obtain ⟨w, hw, hwlinear, α, hα, hnormal⟩ := exists_primePowerIterate_normalForm p f hf hlinear
    hinfinite n (by simpa only [sub_add_cancel] using hdiv n) (hfast n)
  obtain ⟨H, hH0, hHlinear, hHres⟩ := exists_truncated_residue_coordinate π hπ (e + 1) (by omega)
    w hw hwlinear
  subst w
  let hPadm := frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP
  let hGadm := isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) G f hf
    (by rw [hlinear]; exact isUnit_one) hres
  let GN := truncatedSubstIterate π hπ (e + 1) (by omega) G hGadm (p ^ n)
  let hGN := isAdmissible_truncatedSubstIterate π hπ (e + 1) (by omega) G hGadm (p ^ n)
  have hGNres : mapRingHom (residue π hπ (e + 1) (by omega)) GN =
      HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) :=
    residue_truncatedSubstIterate π hπ (e + 1) (by omega) G hGadm f hf
      (by rw [hlinear]; exact isUnit_one) hres (p ^ n)
  let PH := coordinateConjugate π hπ (e + 1) (by omega) P hPadm H hH0 hHlinear
  let GH := coordinateConjugate π hπ (e + 1) (by omega) GN hGN H hH0 hHlinear
  have hPH := residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hH0 hHlinear
  have hsPH : derivativeLevel π hπ p e u hu hpe PH hPH = e := by
    rw [derivativeLevel_coordinateConjugate π hπ p e ε u hu hpe P hP H hH0 hHlinear, hs]
  have hGH : mapRingHom (residue π hπ (e + 1) (by omega)) GH - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1) := by
    rw [residue_coordinateConjugate_ofPowerSeries π hπ (e + 1) (by omega) GN hGN
      (powerSeriesIterate f (p ^ n)) (powerSeriesIterate_spec f hf _).1
      (by rw [(powerSeriesIterate_spec f hf _).2, hlinear, one_pow]; exact isUnit_one)
      hGNres H hH0 hHlinear]
    exact hnormal
  have hcommH := (coordinateConjugate_commute_iff π hπ (e + 1) (by omega) P GN hPadm hGN
    H hH0 hHlinear).mpr (truncatedSubstIterate_commute π hπ (e + 1) (by omega) P G hPadm hGadm hcomm (p ^ n))
  have hbound := order_normalizedDerivative_le_of_top π hπ p e ε u hu hpe PH hPH hsPH
    GH d hd (by simpa only [d, sub_add_cancel] using hdiv n) α hα hGH hcommH
  have horder := order_normalizedDerivative_coordinateConjugate π hπ p e ε u hu hpe P hP H hH0 hHlinear
  rw [horder] at hbound
  change m ≤ (p : ℤ) - 1 - d at hbound
  omega

end FalseTateNonliftability.CoefficientRing
