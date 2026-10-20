/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Admissible
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Canonical finite-level Laurent substitution

Admissibility is finite positive order of the actual coefficient reduction.
Actual nilpotent Laurent evaluation supplies substitution; continuity makes
it independent of the decomposition and exponent. Power-series coordinate
inverses give mutually inverse substitutions on the same Laurent carrier.

This proves blueprint lemmas `nl:finite-level-substitution` and
`nl:power-series-inverse-substitution`.
-/

@[expose] public section

namespace LaurentSeries

open Filter
open scoped Topology

noncomputable section

variable {R : Type*} [CommRing R]

/-- The actual coefficient reduction has finite positive Laurent order. -/
def IsAdmissible (δ : R) (G : LaurentSeries R) : Prop :=
  ∃ a : ℤ, 0 < a ∧ (principalReduction δ G).orderTop = (a : WithTop ℤ)

private theorem exists_pos_nilpotent_exponent (δ : R) (hδ : IsNilpotent δ) :
    ∃ r : ℕ, 1 ≤ r ∧ δ ^ r = 0 := by
  obtain ⟨r, hr⟩ := hδ
  exact ⟨r + 1, Nat.le_add_left 1 r, by rw [pow_succ, hr, zero_mul]⟩

variable (δ : R) (hδ : IsNilpotent δ) [(Ideal.span ({δ} : Set R)).IsMaximal]

include hδ in
/-- Actual evaluation supplies a continuous algebra homomorphism and its chain rule. -/
theorem exists_actual_substitution (G : LaurentSeries R) (hG : IsAdmissible δ G) :
    ∃ F : LaurentSeries R →ₐ[R] LaurentSeries R,
      @Continuous _ _ (orderTopology R) (orderTopology R) F ∧
      F (HahnSeries.single (1 : ℤ) (1 : R)) = G ∧
      ∀ f, derivative R (F f) = F (derivative R f) * derivative R G := by
  obtain ⟨a, ha, horder⟩ := hG
  obtain ⟨r, hr, hpow⟩ := exists_pos_nilpotent_exponent δ hδ
  obtain ⟨U, Y, c, _, hdecomp, hUorder, hUunit, hc, hY⟩ :=
    exists_nilpotentLaurentEval_data δ G r hpow a horder
  let F := nilpotentLaurentEval δ U Y r hr hpow a c ha hc hUorder.ge hY hUunit
  refine ⟨F, continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _, ?_, ?_⟩
  · exact (nilpotentLaurentEval_X δ U Y r hr hpow a c ha hc hUorder.ge hY hUunit).trans
      hdecomp.symm
  · intro f
    simpa only [← hdecomp] using
      derivative_nilpotentLaurentEval δ U Y r hr hpow a c ha hc hUorder.ge hY hUunit f

/-- Canonical substitution constructed from the actual admissible decomposition. -/
def subst (G : LaurentSeries R) (hG : IsAdmissible δ G) :
    LaurentSeries R →ₐ[R] LaurentSeries R :=
  Classical.choose (exists_actual_substitution δ hδ G hG)

/-- Substitution is continuous for the explicitly named order topology. -/
theorem continuous_subst (G : LaurentSeries R) (hG : IsAdmissible δ G) :
    @Continuous _ _ (orderTopology R) (orderTopology R) (subst δ hδ G hG) :=
  (Classical.choose_spec (exists_actual_substitution δ hδ G hG)).1

@[simp]
theorem subst_X (G : LaurentSeries R) (hG : IsAdmissible δ G) :
    subst δ hδ G hG (HahnSeries.single (1 : ℤ) (1 : R)) = G :=
  (Classical.choose_spec (exists_actual_substitution δ hδ G hG)).2.1

/-- The actual canonical derivative satisfies the substitution chain rule. -/
theorem derivative_subst (G : LaurentSeries R) (hG : IsAdmissible δ G) (f : LaurentSeries R) :
    derivative R (subst δ hδ G hG f) =
      subst δ hδ G hG (derivative R f) * derivative R G :=
  (Classical.choose_spec (exists_actual_substitution δ hδ G hG)).2.2 f

/-- A continuous algebra homomorphism sending the variable to `G` is substitution.
This includes independence of all actual decomposition and exponent choices. -/
theorem subst_unique (G : LaurentSeries R) (hG : IsAdmissible δ G)
    (F : LaurentSeries R →ₐ[R] LaurentSeries R)
    (hF : @Continuous _ _ (orderTopology R) (orderTopology R) F)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) = G) : F = subst δ hδ G hG := by
  let := orderTopology R
  have := orderTopology_t2Space (R := R)
  apply continuous_algHom_ext_X F (subst δ hδ G hG) hF (continuous_subst δ hδ G hG)
  exact hX.trans (subst_X δ hδ G hG).symm

include hδ in
/-- Every admissible series is an actual Laurent unit. -/
theorem IsAdmissible.isUnit {G : LaurentSeries R} (hG : IsAdmissible δ G) : IsUnit G := by
  have hX : IsUnit (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) :=
    IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : R)) (by simp)
  simpa only [subst_X] using hX.map (subst δ hδ G hG)

/-- Canonical substitution agrees with any actual nilpotent evaluation having
the same variable image, even with a different perturbation coefficient. -/
theorem subst_eq_nilpotentLaurentEval (G : LaurentSeries R) (hG : IsAdmissible δ G)
    (ε : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hpow : ε ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)
    (hdecomp : G = U + HahnSeries.C ε * Y) :
    subst δ hδ G hG = nilpotentLaurentEval ε U Y r hr hpow a c ha hc hU hY hUunit := by
  symm
  apply subst_unique δ hδ G hG _ (continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _)
  exact (nilpotentLaurentEval_X ε U Y r hr hpow a c ha hc hU hY hUunit).trans hdecomp.symm

private theorem orderTop_principalReduction_zero (f : LaurentSeries R) :
    (principalReduction (0 : R) f).orderTop = f.orderTop := by
  apply orderTop_mapRingHom_of_injective
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_zero]

/-- Reduction modulo zero preserves exactly the finite positive order condition. -/
theorem isAdmissible_zero_iff (G : LaurentSeries R) :
    IsAdmissible (0 : R) G ↔ ∃ a : ℤ, 0 < a ∧ G.orderTop = (a : WithTop ℤ) := by
  simp only [IsAdmissible, orderTop_principalReduction_zero]

omit [(Ideal.span ({δ} : Set R)).IsMaximal] in
/-- An admissible series reduces to an admissible series over the coefficient field. -/
theorem IsAdmissible.reduced {G : LaurentSeries R} (hG : IsAdmissible δ G) :
    IsAdmissible (0 : R ⧸ Ideal.span {δ}) (principalReduction δ G) := by
  rw [isAdmissible_zero_iff]
  exact hG

local instance quotientField : Field (R ⧸ Ideal.span {δ}) := Ideal.Quotient.field _

local instance zeroSpanIsMaximal {k : Type*} [Field k] :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- Zero-perturbation evaluation has exponent one and no order loss. -/
theorem subst_zero_mem_orderAddSubgroup {k : Type*} [Field k]
    (G : LaurentSeries k) (hG : IsAdmissible (0 : k) G)
    (a : ℤ) (ha : 0 < a) (horder : G.orderTop = (a : WithTop ℤ))
    (N : ℕ) (f : LaurentSeries k) (hf : f ∈ orderAddSubgroup (N : ℤ)) :
    subst 0 IsNilpotent.zero G hG f ∈ orderAddSubgroup (a * N) := by
  have heq := subst_eq_nilpotentLaurentEval 0 IsNilpotent.zero G hG
    0 G 0 1 (by omega) (by simp) a 0 ha le_rfl horder.ge (by simp)
      (hG.isUnit 0 IsNilpotent.zero) (by simp)
  rw [heq]
  simpa only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero] using
    nilpotentLaurentEval_mem_orderAddSubgroup 0 G 0 1 (by omega) (by simp)
      a 0 ha le_rfl horder.ge (by simp) (hG.isUnit 0 IsNilpotent.zero) N f hf

/-- Actual substitution commutes with principal coefficient reduction. The target
uses the coefficient field and distinguished element zero. -/
theorem principalReduction_subst (G : LaurentSeries R) (hG : IsAdmissible δ G)
    (f : LaurentSeries R) :
    principalReduction δ (subst δ hδ G hG f) =
      subst 0 IsNilpotent.zero (principalReduction δ G) hG.reduced
        (principalReduction δ f) := by
  obtain ⟨a, ha, horder⟩ := hG
  obtain ⟨r, hr, hpow⟩ := exists_pos_nilpotent_exponent δ hδ
  obtain ⟨U, Y, c, _, hdecomp, hUorder, hUunit, hc, hY⟩ :=
    exists_nilpotentLaurentEval_data δ G r hpow a horder
  let q := Ideal.Quotient.mk (Ideal.span ({δ} : Set R))
  let E := nilpotentLaurentEval (q δ) (mapRingHom q U) (mapRingHom q Y) r hr
    (by simpa only [map_pow, map_zero] using congrArg q hpow) a c ha hc
    (hUorder.ge.trans (orderTop_le_mapRingHom q U))
    (hY.trans (orderTop_le_mapRingHom q Y)) (hUunit.map (mapRingHom q))
  have hE : E = subst 0 IsNilpotent.zero (principalReduction δ G)
      (IsAdmissible.reduced δ ⟨a, ha, horder⟩) := by
    apply subst_unique _ _ _ _ E (continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _)
    change E (HahnSeries.single (1 : ℤ) 1) = mapRingHom q G
    rw [nilpotentLaurentEval_X, hdecomp, map_add, map_mul, mapRingHom_C]
  rw [subst_eq_nilpotentLaurentEval δ hδ G ⟨a, ha, horder⟩
    δ U Y r hr hpow a c ha hc hUorder.ge hY hUunit hdecomp]
  exact (mapRingHom_nilpotentLaurentEval q δ U Y r hr hpow a c ha hc hUorder.ge hY hUunit f).trans
    (congrArg (fun F : LaurentSeries (R ⧸ Ideal.span {δ}) →ₐ[R ⧸ Ideal.span {δ}]
      LaurentSeries (R ⧸ Ideal.span {δ}) ↦ F (principalReduction δ f)) hE)

include hδ in
/-- Admissibility is preserved by actual substitution. Positivity uses the
normalized exponent-one estimate; nonvanishing follows from preservation of units. -/
theorem IsAdmissible.substitution {G H : LaurentSeries R}
    (hG : IsAdmissible δ G) (hH : IsAdmissible δ H) :
    IsAdmissible δ (subst δ hδ H hH G) := by
  have hnonzero : principalReduction δ (subst δ hδ H hH G) ≠ 0 := by
    have hu := ((hG.isUnit δ hδ).map (subst δ hδ H hH)).map (principalReduction δ)
    exact hu.ne_zero
  obtain ⟨a, ha, hGorder⟩ := show ∃ a : ℤ, 0 < a ∧
    (principalReduction δ G).orderTop = (a : WithTop ℤ) from hG
  obtain ⟨b, hb, hHorder⟩ := show ∃ b : ℤ, 0 < b ∧
    (principalReduction δ H).orderTop = (b : WithTop ℤ) from hH
  have hG1 : principalReduction δ G ∈ orderAddSubgroup 1 :=
    orderAddSubgroup_antitone (show 1 ≤ a by omega) hGorder.ge
  have hbound : principalReduction δ (subst δ hδ H hH G) ∈ orderAddSubgroup b := by
    rw [principalReduction_subst δ hδ H hH G]
    simpa only [Nat.cast_one, mul_one] using
      subst_zero_mem_orderAddSubgroup (principalReduction δ H)
        hH.reduced b hb hHorder 1
        (principalReduction δ G) hG1
  have hpos : 0 < (principalReduction δ (subst δ hδ H hH G)).order := by
    apply (HahnSeries.zero_lt_orderTop_iff hnonzero).mp
    exact (WithTop.coe_lt_coe.mpr hb).trans_le hbound
  exact ⟨_, hpos, (HahnSeries.order_eq_orderTop_of_ne_zero hnonzero).symm⟩

/-- Composition of the actual continuous substitutions is substitution at the
actual substituted parameter. -/
theorem subst_comp (G H : LaurentSeries R) (hG : IsAdmissible δ G) (hH : IsAdmissible δ H) :
    (subst δ hδ H hH).comp (subst δ hδ G hG) =
      subst δ hδ (subst δ hδ H hH G) (hG.substitution δ hδ hH) := by
  let := orderTopology R
  apply subst_unique δ hδ _ _ ((subst δ hδ H hH).comp (subst δ hδ G hG))
    ((continuous_subst δ hδ H hH).comp (continuous_subst δ hδ G hG))
  simp only [AlgHom.comp_apply, subst_X]

/-- Associativity on admissible parameters, with arbitrary Laurent input. -/
theorem subst_assoc (G H : LaurentSeries R) (hG : IsAdmissible δ G) (hH : IsAdmissible δ H)
    (f : LaurentSeries R) :
    subst δ hδ H hH (subst δ hδ G hG f) =
      subst δ hδ (subst δ hδ H hH G) (hG.substitution δ hδ hH) f :=
  AlgHom.congr_fun (subst_comp δ hδ G H hG hH) f

private theorem ofPowerSeries_mem_orderAddSubgroup_one (P : PowerSeries R)
    (hP : P.constantCoeff = 0) : HahnSeries.ofPowerSeries ℤ R P ∈ orderAddSubgroup 1 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [PowerSeries.coeff_coe]
  by_cases hj0 : j < 0
  · rw [ite_eq_left hj0]
  · have hjz : j = 0 := by omega
    subst j
    simpa only [lt_self_iff_false, ite_false, Int.natAbs_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP

/-- A zero-constant power series with unit linear coefficient has reduced order one. -/
theorem isAdmissible_ofPowerSeries (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) : IsAdmissible δ (HahnSeries.ofPowerSeries ℤ R P) := by
  refine ⟨1, by omega, le_antisymm ?_ ?_⟩
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    have hunit := hlinear.map (Ideal.Quotient.mk (Ideal.span ({δ} : Set R)))
    have hcoeff : IsUnit ((principalReduction δ (HahnSeries.ofPowerSeries ℤ R P)).coeff 1) := by
      simpa only [principalReduction_coeff, show (1 : ℤ) = (1 : ℕ) from rfl,
        HahnSeries.ofPowerSeries_apply_coeff] using hunit
    exact hcoeff.ne_zero
  · exact mapRingHom_mem_orderAddSubgroup _ _ _ (ofPowerSeries_mem_orderAddSubgroup_one P hP)

/-- On every embedded power series, actual Laurent substitution is ordinary
power-series substitution. Its coefficients are the same actual finite sums. -/
theorem subst_ofPowerSeries (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : PowerSeries R) :
    subst δ hδ (HahnSeries.ofPowerSeries ℤ R P) (isAdmissible_ofPowerSeries δ P hP hlinear)
      (HahnSeries.ofPowerSeries ℤ R f) = HahnSeries.ofPowerSeries ℤ R (f.subst P) := by
  have hadm := isAdmissible_ofPowerSeries δ P hP hlinear
  have hbound : (1 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ R P).orderTop :=
    ofPowerSeries_mem_orderAddSubgroup_one P hP
  have hunit := hadm.isUnit δ hδ
  rw [subst_eq_nilpotentLaurentEval δ hδ _ hadm 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
    (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) hunit (by simp),
    nilpotentLaurentEval_ofPowerSeries]
  ext j
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, nilpotentPowerSeriesEval_coeff,
      HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hP)]
    apply finsum_congr
    intro d
    simp only [map_zero, zero_mul, add_zero,
      ← map_pow (HahnSeries.ofPowerSeries ℤ R), HahnSeries.ofPowerSeries_apply_coeff]
  | negSucc n =>
    have hz : nilpotentPowerSeriesEval 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
        (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) f ∈ orderAddSubgroup 0 := by
      simpa only [Nat.cast_zero, mul_zero, Nat.sub_self, zero_mul, sub_zero] using
        nilpotentPowerSeriesEval_mem_orderAddSubgroup 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
          (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) 0 f (by intro n hn; omega)
    rw [(mem_orderAddSubgroup_iff_coeff _ _).mp hz (Int.negSucc n) (by omega),
      PowerSeries.coeff_coe, ite_eq_left (Int.negSucc_lt_zero n)]

omit [(Ideal.span ({δ} : Set R)).IsMaximal] in
/-- A zero-constant coordinate with unit linear coefficient has a unique
zero-constant two-sided compositional inverse, supplied by Mathlib. -/
theorem exists_unique_powerSeries_subst_inverse (P : PowerSeries R)
    (hP : P.constantCoeff = 0) (hlinear : IsUnit (P.coeff 1)) :
    ∃! Q : PowerSeries R, Q.constantCoeff = 0 ∧ P.subst Q = PowerSeries.X ∧
      Q.subst P = PowerSeries.X := by
  refine ⟨P.substInvOfIsUnit hlinear, ⟨PowerSeries.constantCoeff_substInvOfIsUnit P hlinear,
    PowerSeries.subst_substInvOfIsUnit_right P hP hlinear,
    PowerSeries.subst_substInvOfIsUnit_left P hP hlinear⟩, ?_⟩
  intro Q hQ
  exact PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X P hP hlinear
    (PowerSeries.HasSubst.of_constantCoeff_zero' hQ.1) hQ.2.1

/-- A power-series inverse identity gives an identity of the actual continuous
Laurent substitutions, through their coefficientwise restriction formula. -/
theorem subst_ofPowerSeries_comp_eq_id (P Q : PowerSeries R)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0)
    (hPlinear : IsUnit (P.coeff 1)) (hQlinear : IsUnit (Q.coeff 1))
    (hQP : Q.subst P = PowerSeries.X) :
    (subst δ hδ (HahnSeries.ofPowerSeries ℤ R P) (isAdmissible_ofPowerSeries δ P hP hPlinear)).comp
      (subst δ hδ (HahnSeries.ofPowerSeries ℤ R Q) (isAdmissible_ofPowerSeries δ Q hQ hQlinear)) =
        AlgHom.id R (LaurentSeries R) := by
  let := orderTopology R
  have := orderTopology_t2Space (R := R)
  let FP := subst δ hδ (HahnSeries.ofPowerSeries ℤ R P) (isAdmissible_ofPowerSeries δ P hP hPlinear)
  let FQ := subst δ hδ (HahnSeries.ofPowerSeries ℤ R Q) (isAdmissible_ofPowerSeries δ Q hQ hQlinear)
  have hFP : Continuous FP := continuous_subst δ hδ _ _
  have hFQ : Continuous FQ := continuous_subst δ hδ _ _
  apply continuous_algHom_ext_X (FP.comp FQ) (AlgHom.id R (LaurentSeries R))
    (hFP.comp hFQ) continuous_id
  simp only [FP, FQ, AlgHom.comp_apply, AlgHom.id_apply, subst_X]
  rw [subst_ofPowerSeries δ hδ P hP hPlinear Q, hQP, HahnSeries.ofPowerSeries_X]

/-- The actual Laurent substitutions at a power-series coordinate and its
Mathlib compositional inverse, packaged as an algebra automorphism. -/
def powerSeriesSubstEquiv (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) : LaurentSeries R ≃ₐ[R] LaurentSeries R := by
  let Q := P.substInvOfIsUnit hlinear
  have hQ : Q.constantCoeff = 0 := PowerSeries.constantCoeff_substInvOfIsUnit P hlinear
  have hQlinear : IsUnit (Q.coeff 1) := by
    rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact Units.isUnit _
  exact AlgEquiv.ofAlgHom
    (subst δ hδ (HahnSeries.ofPowerSeries ℤ R P) (isAdmissible_ofPowerSeries δ P hP hlinear))
    (subst δ hδ (HahnSeries.ofPowerSeries ℤ R Q) (isAdmissible_ofPowerSeries δ Q hQ hQlinear))
    (subst_ofPowerSeries_comp_eq_id δ hδ P Q hP hQ hlinear hQlinear
      (PowerSeries.subst_substInvOfIsUnit_left P hP hlinear))
    (subst_ofPowerSeries_comp_eq_id δ hδ Q P hQ hP hQlinear hlinear
      (PowerSeries.subst_substInvOfIsUnit_right P hP hlinear))

@[simp]
theorem powerSeriesSubstEquiv_apply (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : LaurentSeries R) :
    powerSeriesSubstEquiv δ hδ P hP hlinear f =
      subst δ hδ (HahnSeries.ofPowerSeries ℤ R P) (isAdmissible_ofPowerSeries δ P hP hlinear) f := rfl

/-- The inverse automorphism is exactly actual substitution at Mathlib's
zero-constant inverse coordinate. -/
theorem powerSeriesSubstEquiv_symm_apply (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : LaurentSeries R) :
    (powerSeriesSubstEquiv δ hδ P hP hlinear).symm f =
      subst δ hδ (HahnSeries.ofPowerSeries ℤ R (P.substInvOfIsUnit hlinear))
        (isAdmissible_ofPowerSeries δ _ (PowerSeries.constantCoeff_substInvOfIsUnit P hlinear)
          (by rw [PowerSeries.coeff_one_substInvOfIsUnit]; exact Units.isUnit _)) f := rfl

/-- Continuity of the actual coordinate automorphism in the named order topology. -/
theorem continuous_powerSeriesSubstEquiv (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) :
    @Continuous _ _ (orderTopology R) (orderTopology R) (powerSeriesSubstEquiv δ hδ P hP hlinear) :=
  continuous_subst δ hδ _ _

/-- Its actual inverse substitution is continuous for that same topology. -/
theorem continuous_powerSeriesSubstEquiv_symm (P : PowerSeries R) (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) :
    @Continuous _ _ (orderTopology R) (orderTopology R)
      (powerSeriesSubstEquiv δ hδ P hP hlinear).symm :=
  continuous_subst δ hδ _ _

end

end LaurentSeries
