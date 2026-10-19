module

public import FalseTateNonliftability.CoefficientRing.Graded
public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.LaurentSeries.CharacteristicP
public import FontaineWintenberger.Ramification.Degree
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Finite coefficient layers and normalized derivatives

All layers are those of the actual finite coefficient quotient. Normalization
uses the inverse of `gradedLayerEquiv`, not division by a nilpotent element.

The actual derivative has a unique nonzero first layer, the two coefficient
forms, and the commuting-substitution law. Actual power-series coordinate
conjugacy preserves its first level and normalized Laurent order. Prime-field
Frobenius is proved using a residue equivalence, which is constructed for the
actual finite totally ramified p-adic coefficient extension.

This proves the finite-level assertions of `nl:normalized-derivative`.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O]

/-- The canonical Laurent derivative restricts to the canonical power-series derivative. -/
theorem derivative_ofPowerSeries (H : PowerSeries O) :
    derivative O (HahnSeries.ofPowerSeries ℤ O H) =
      HahnSeries.ofPowerSeries ℤ O (PowerSeries.derivative H) :=
  LaurentSeries.derivative_ofPowerSeries H

/-- A power-series coordinate with unit linear coefficient has a unit actual
Laurent derivative over an arbitrary commutative coefficient ring. -/
theorem isUnit_derivative_ofPowerSeries (H : PowerSeries O) (hlinear : IsUnit (H.coeff 1)) :
    IsUnit (derivative O (HahnSeries.ofPowerSeries ℤ O H)) :=
  LaurentSeries.isUnit_derivative_ofPowerSeries H hlinear

private theorem order_eq_of_coefficient (f : LaurentSeries O) (m : ℤ)
    (hm : f.coeff m ≠ 0) (hbelow : ∀ j < m, f.coeff j = 0) : f.order = m := by
  have ht := HahnSeries.orderTop_eq_of_le (HahnSeries.mem_support _ _ |>.mpr hm)
    (fun j hj ↦ by
      by_contra h
      exact (HahnSeries.mem_support _ _ |>.mp hj) (hbelow j (lt_of_not_ge h)))
  exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hm)).trans ht

private theorem order_ofPowerSeries_of_constantCoeff_ne_zero (H : PowerSeries O)
    (hH : H.constantCoeff ≠ 0) : (HahnSeries.ofPowerSeries ℤ O H).order = 0 := by
  apply order_eq_of_coefficient
  · simpa only [show (0 : ℤ) = (0 : ℕ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hH
  · intro j hj
    rw [PowerSeries.coeff_coe, ite_eq_left hj]

section ResidueCoordinateOrder

variable {k : Type*} [Field k]

local instance : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The derivative of an actual residue coordinate has Laurent order zero. -/
theorem order_derivative_ofPowerSeries (H : PowerSeries k) (hlinear : IsUnit (H.coeff 1)) :
    (derivative k (HahnSeries.ofPowerSeries ℤ k H)).order = 0 := by
  rw [derivative_ofPowerSeries]
  apply order_ofPowerSeries_of_constantCoeff_ne_zero
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hlinear.ne_zero

private theorem order_pow_of_order_zero (x : LaurentSeries k) (hx : x ≠ 0)
    (horder : x.order = 0) (n : ℕ) : (x ^ n).order = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hx) hx, ih, horder, zero_add]

/-- The canonical power-series coordinate automorphism over a field preserves
the actual Laurent order, including negative orders. The proof uses its
integer monomials and the actual power-series part, not a nilpotent tail bound. -/
theorem order_powerSeriesSubstEquiv (H : PowerSeries k) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (f : LaurentSeries k) :
    (powerSeriesSubstEquiv 0 IsNilpotent.zero H hzero hlinear f).order = f.order := by
  let E := powerSeriesSubstEquiv (0 : k) IsNilpotent.zero H hzero hlinear
  have hEne (m : ℤ) : E (HahnSeries.single m 1) ≠ 0 := by
    intro h
    apply HahnSeries.single_ne_zero (a := m) (one_ne_zero : (1 : k) ≠ 0)
    apply E.injective
    simpa only [map_zero] using h
  have hHorder : (HahnSeries.ofPowerSeries ℤ k H).order = 1 := by
    apply order_eq_of_coefficient
    · simpa only [show (1 : ℤ) = (1 : ℕ) from rfl,
        HahnSeries.ofPowerSeries_apply_coeff] using hlinear.ne_zero
    · intro j hj
      rw [PowerSeries.coeff_coe]
      by_cases hj0 : j < 0
      · rw [ite_eq_left hj0]
      · have hjz : j = 0 := by omega
        subst j
        simpa only [lt_self_iff_false, ite_false, Int.natAbs_zero,
          PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
  have hX : E (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k H :=
    subst_X 0 IsNilpotent.zero _ _
  have hn (n : ℕ) : (E (HahnSeries.single (n : ℤ) 1)).order = n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hm : (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1 : LaurentSeries k) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by
        simp [HahnSeries.single_mul_single]
      rw [hm, map_mul, HahnSeries.order_mul (hEne _) (hEne _), ih, hX, hHorder]
      simp only [Nat.cast_add, Nat.cast_one]
  have hz (m : ℤ) : (E (HahnSeries.single m 1)).order = m := by
    cases m with
    | ofNat n => exact hn n
    | negSucc n =>
      have hm : (Int.negSucc n : ℤ) + ((n + 1 : ℕ) : ℤ) = 0 := by omega
      have hprod : E (HahnSeries.single (Int.negSucc n) 1) *
          E (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1) = 1 := by
        rw [← map_mul, HahnSeries.single_mul_single, hm, one_mul]
        simp
      have ho := congrArg HahnSeries.order hprod
      rw [HahnSeries.order_mul (hEne _) (hEne _), hn, HahnSeries.order_one] at ho
      omega
  by_cases hf : f = 0
  · subst f
    simp
  have hpart : f.powerSeriesPart.constantCoeff ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff,
      Nat.cast_zero, add_zero] using (HahnSeries.coeff_order_eq_zero.not.mpr hf)
  have hsubst : (f.powerSeriesPart.subst H).constantCoeff = f.powerSeriesPart.constantCoeff := by
    simpa only [Algebra.algebraMap_self_apply] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hzero f.powerSeriesPart
  have hpartOrder : (E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart)).order = 0 := by
    rw [powerSeriesSubstEquiv_apply,
      subst_ofPowerSeries 0 IsNilpotent.zero H hzero hlinear f.powerSeriesPart]
    exact order_ofPowerSeries_of_constantCoeff_ne_zero _ (hsubst ▸ hpart)
  have hpartUnit : IsUnit (E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart)) :=
    ((PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hpart)).map
      (HahnSeries.ofPowerSeries ℤ k)).map E
  have heq : E f = E (HahnSeries.single f.order 1) *
      E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart) :=
    (congrArg E (single_order_mul_powerSeriesPart f)).symm.trans (map_mul E _ _)
  rw [heq, HahnSeries.order_mul (hEne _) hpartUnit.ne_zero, hz, hpartOrder, add_zero]

end ResidueCoordinateOrder

section PrimeField

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

local instance : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

omit [CharP k p] in
/-- The actual positive monomial is an admissible residue substitution. -/
theorem primeMonomial_isAdmissible :
    IsAdmissible (0 : k) (HahnSeries.single (p : ℤ) (1 : k)) := by
  rw [isAdmissible_zero_iff]
  exact ⟨p, by exact_mod_cast (Fact.out : p.Prime).pos,
    HahnSeries.orderTop_single one_ne_zero⟩

/-- Over the actual prime residue field, substitution at `T^p` is Frobenius.
The prime-field equivalence is essential: perfectness alone does not fix coefficients. -/
theorem subst_primeMonomial_eq_pow (ε : k ≃+* ZMod p) (f : LaurentSeries k) :
    subst 0 IsNilpotent.zero (HahnSeries.single (p : ℤ) 1)
      (primeMonomial_isAdmissible (k := k) p) f = f ^ p := by
  let := orderTopology k
  let := orderTopology_isTopologicalRing (R := k)
  let := orderTopology_t2Space (R := k)
  let : CharP (LaurentSeries k) p :=
    charP_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective p
  have hfix (x : k) : x ^ p = x := by
    apply ε.injective
    simpa only [map_pow] using ZMod.pow_card (ε x)
  let F : LaurentSeries k →ₐ[k] LaurentSeries k :=
    { frobenius (LaurentSeries k) p with
      commutes' := by
        intro x
        change (algebraMap k (LaurentSeries k) x) ^ p = algebraMap k (LaurentSeries k) x
        rw [← map_pow, hfix] }
  have hF : Continuous F := by
    change Continuous (fun f : LaurentSeries k ↦ f ^ p)
    exact continuous_pow p
  have hX : F (HahnSeries.single (1 : ℤ) 1) = HahnSeries.single (p : ℤ) 1 := by
    change (HahnSeries.single (1 : ℤ) (1 : k)) ^ p = _
    simp only [HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]
  exact congrArg (fun E : LaurentSeries k →ₐ[k] LaurentSeries k ↦ E f)
    (subst_unique 0 IsNilpotent.zero _ (primeMonomial_isAdmissible (k := k) p) F hF hX).symm

end PrimeField

/-- The original principal filtration decreases with the index. -/
theorem layerIdeal_antitone (π : O) (r : ℕ) {i j : ℕ} (hij : i ≤ j) :
    layerIdeal π r j ≤ layerIdeal π r i :=
  span_pow_le (HahnSeries.C (parameter π r) : LaurentSeries (Truncation π r)) hij

@[simp]
theorem layerIdeal_zero (π : O) (r : ℕ) : layerIdeal π r 0 = ⊤ := by
  simp only [layerIdeal, pow_zero, Ideal.span_singleton_one]

/-- The actual defining nilpotence relation terminates the finite filtration. -/
@[simp]
theorem layerIdeal_self (π : O) (r : ℕ) : layerIdeal π r r = ⊥ := by
  rw [layerIdeal, ← map_pow (HahnSeries.C : Truncation π r →+* LaurentSeries (Truncation π r)),
    parameter_pow_eq_zero, map_zero, Ideal.span_singleton_zero]

/-- Every actual coefficient algebra homomorphism preserves the principal layers. -/
theorem algHom_mem_layerIdeal (π : O) (r : ℕ)
    (E : LaurentSeries (Truncation π r) →ₐ[Truncation π r] LaurentSeries (Truncation π r))
    (j : ℕ) (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) :
    E X ∈ layerIdeal π r j := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  have hC : E (HahnSeries.C (parameter π r)) = HahnSeries.C (parameter π r) := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using E.commutes (parameter π r)
  rw [hY, map_mul, map_pow, hC]
  exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩

/-- An actual coefficient algebra automorphism preserves every principal layer
in both directions; this applies to the canonical power-series coordinate map. -/
theorem algEquiv_mem_layerIdeal_iff (π : O) (r : ℕ)
    (E : LaurentSeries (Truncation π r) ≃ₐ[Truncation π r] LaurentSeries (Truncation π r))
    (j : ℕ) (X : LaurentSeries (Truncation π r)) :
    E X ∈ layerIdeal π r j ↔ X ∈ layerIdeal π r j := by
  constructor
  · intro h
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
      algHom_mem_layerIdeal π r E.symm.toAlgHom j (E X) h
  · exact algHom_mem_layerIdeal π r E.toAlgHom j X

private theorem exists_layer_boundary (π : O) (r : ℕ)
    (X : LaurentSeries (Truncation π r)) (n : ℕ) (hn : X ∉ layerIdeal π r n) :
    ∃ s, s < n ∧ X ∈ layerIdeal π r s ∧ X ∉ layerIdeal π r (s + 1) := by
  induction n with
  | zero => exact False.elim (hn (by simp))
  | succ n ih =>
    by_cases h : X ∈ layerIdeal π r n
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · obtain ⟨s, hs, hmem, hnot⟩ := ih h
      exact ⟨s, hs.trans (Nat.lt_succ_self n), hmem, hnot⟩

/-- Every actual nonzero element in the first ideal has a unique first nonzero
finite coefficient layer. No layer or nonvanishing identification is assumed. -/
theorem exists_unique_first_layer (π : O) (r : ℕ)
    (X : LaurentSeries (Truncation π r)) (hX : X ≠ 0) (hfirst : X ∈ layerIdeal π r 1) :
    ∃! s : ℕ, 1 ≤ s ∧ s < r ∧ X ∈ layerIdeal π r s ∧ X ∉ layerIdeal π r (s + 1) := by
  obtain ⟨s, hsr, hs, hsn⟩ := exists_layer_boundary π r X r (by simpa using hX)
  have hspos : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    subst s
    exact hsn hfirst
  refine ⟨s, ⟨hspos, hsr, hs, hsn⟩, ?_⟩
  intro t ht
  have hst : ¬ s < t := by
    intro h
    exact hsn (layerIdeal_antitone π r (show s + 1 ≤ t by omega) ht.2.2.1)
  have hts : ¬ t < s := by
    intro h
    exact ht.2.2.2 (layerIdeal_antitone π r (show t + 1 ≤ s by omega) hs)
  omega

section DiscreteValuationRing

variable [IsDomain O] [IsDiscreteValuationRing O] (π : O) (hπ : Irreducible π)

local instance residueZeroSpanIsMaximal :
    (Ideal.span ({(0 : IsLocalRing.ResidueField O)} : Set (IsLocalRing.ResidueField O))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual residue Laurent series represented by an element of the specified
ideal, obtained by the inverse of the proved original graded-layer equivalence. -/
def layerResidue (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) :
    LaurentSeries (IsLocalRing.ResidueField O) :=
  (gradedLayerEquiv π hπ r j hjr).symm
    (Submodule.Quotient.mk (⟨X, hX⟩ : layerSubmodule π r j))

/-- The actual normalization vanishes exactly on the next original ideal. -/
theorem layerResidue_eq_zero_iff (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) :
    layerResidue π hπ r j hjr X hX = 0 ↔ X ∈ layerIdeal π r (j + 1) := by
  change (gradedLayerEquiv π hπ r j hjr).symm
    (Submodule.Quotient.mk (⟨X, hX⟩ : layerSubmodule π r j)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  rfl

/-- Every first nonzero layer normalizes to an actual nonzero residue series. -/
theorem layerResidue_ne_zero_iff (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) :
    layerResidue π hπ r j hjr X hX ≠ 0 ↔ X ∉ layerIdeal π r (j + 1) :=
  not_congr (layerResidue_eq_zero_iff π hπ r j hjr X hX)

/-- Normalization of an actual uniformizer multiple computes original coefficient residue. -/
@[simp]
theorem layerResidue_C_pow_mul (r j : ℕ) (hjr : j < r)
    (g : LaurentSeries (Truncation π r)) :
    layerResidue π hπ r j hjr ((HahnSeries.C (parameter π r)) ^ j * g)
      (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩) =
        mapRingHom (residue π hπ r (by omega)) g := by
  apply (gradedLayerEquiv π hπ r j hjr).injective
  dsimp only [layerResidue]
  rw [LinearEquiv.apply_symm_apply, gradedLayerEquiv_apply_residue]

omit [IsDiscreteValuationRing O] in
include hπ in
/-- Cancellation in the original coefficient domain gives the actual scalar
graded-kernel computation, including the top nonzero layer. -/
theorem parameter_pow_mul_mem_iff (r j : ℕ) (hjr : j < r) (x : Truncation π r) :
    parameter π r ^ j * x ∈ Ideal.span {parameter π r ^ (j + 1)} ↔
      x ∈ Ideal.span {parameter π r} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  let q := Ideal.Quotient.mk (Ideal.span ({π ^ r} : Set O))
  have hspan (n : ℕ) : (Ideal.span ({π ^ n} : Set O)).map q =
      Ideal.span {parameter π r ^ n} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    rfl
  have hspan_one : (Ideal.span ({π} : Set O)).map q = Ideal.span {parameter π r} := by
    simpa only [pow_one] using hspan 1
  change q π ^ j * q a ∈ Ideal.span {parameter π r ^ (j + 1)} ↔
    q a ∈ Ideal.span {parameter π r}
  have hfirst : Ideal.span ({π ^ r} : Set O) ≤ Ideal.span {π} := by
    simpa only [pow_one] using span_pow_le π (show 1 ≤ r by omega)
  rw [← map_pow q π j, ← map_mul, ← hspan (j + 1), ← hspan_one,
    Ideal.mem_quotient_iff_mem (span_pow_le π (show j + 1 ≤ r by omega)),
    Ideal.mem_quotient_iff_mem hfirst,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem coeff_C_pow_mul (r j : ℕ) (Y : LaurentSeries (Truncation π r)) (n : ℤ) :
    (((HahnSeries.C (parameter π r)) ^ j) * Y).coeff n = parameter π r ^ j * Y.coeff n := by
  rw [← map_pow (HahnSeries.C : Truncation π r →+* LaurentSeries (Truncation π r))
    (parameter π r) j, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
  rfl

/-- Vanishing of a normalized coefficient is actual membership of the original
coefficient in the next scalar ideal. -/
theorem layerResidue_coeff_eq_zero_iff (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) (n : ℤ) :
    (layerResidue π hπ r j hjr X hX).coeff n = 0 ↔
      X.coeff n ∈ Ideal.span {parameter π r ^ (j + 1)} := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  subst X
  have hres := layerResidue_C_pow_mul π hπ r j hjr Y
  rw [hres, mapRingHom_coeff, coeff_C_pow_mul]
  rw [← RingHom.mem_ker, ker_residue π hπ r (by omega)]
  exact (parameter_pow_mul_mem_iff π hπ r j hjr (Y.coeff n)).symm

/-- A known uniformizer multiple in one original coefficient computes the
normalized coefficient through the actual residue map. -/
theorem layerResidue_coeff_eq_of_coeff_eq (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j)
    (n : ℤ) (b : Truncation π r) (hb : X.coeff n = parameter π r ^ j * b) :
    (layerResidue π hπ r j hjr X hX).coeff n = residue π hπ r (by omega) b := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  subst X
  have hres := layerResidue_C_pow_mul π hπ r j hjr Y
  rw [hres, mapRingHom_coeff]
  rw [coeff_C_pow_mul] at hb
  have hdiff : parameter π r ^ j * (Y.coeff n - b) = 0 := by
    rw [mul_sub, hb, sub_self]
  have hmem : Y.coeff n - b ∈ Ideal.span {parameter π r} :=
    (parameter_pow_mul_mem_iff π hπ r j hjr _).mp (by
      rw [hdiff]
      exact Ideal.zero_mem _)
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact show Y.coeff n - b ∈ RingHom.ker (residue π hπ r (by omega)) from
    (ker_residue π hπ r (by omega)).symm ▸ hmem

/-- The first original Laurent ideal is the kernel of the actual residue map. -/
theorem mem_layerIdeal_one_iff (r : ℕ) (hr : 1 ≤ r)
    (X : LaurentSeries (Truncation π r)) :
    X ∈ layerIdeal π r 1 ↔ mapRingHom (residue π hπ r hr) X = 0 := by
  rw [layerIdeal, pow_one, mem_span_C_iff, HahnSeries.ext_iff, funext_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero, ← RingHom.mem_ker,
    ker_residue π hπ r hr]

/-- A coefficient with nonzero actual residue is a unit in the actual truncation. -/
theorem isUnit_of_residue_ne_zero (r : ℕ) (hr : 1 ≤ r) (x : Truncation π r)
    (hx : residue π hπ r hr x ≠ 0) : IsUnit x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit a).mp hx).map (Ideal.Quotient.mk _)

omit [IsDiscreteValuationRing O] in
include hπ in
/-- A unit times exactly the `e`-th uniformizer power survives the actual
quotient modulo the next power. -/
theorem mk_pow_mul_unit_ne_zero (e : ℕ) (u : O) (hu : IsUnit u) :
    Ideal.Quotient.mk (Ideal.span {π ^ (e + 1)}) (π ^ e * u) ≠ 0 := by
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)]
  exact fun h ↦ hπ.not_isUnit (isUnit_of_dvd_unit h hu)

/-- Frobenius reduction forces the actual derivative into the first coefficient ideal. -/
theorem derivative_mem_layerIdeal_one (p r : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (hr : 1 ≤ r) (P : LaurentSeries (Truncation π r))
    (hP : mapRingHom (residue π hπ r hr) P = HahnSeries.single (p : ℤ) 1) :
    derivative (Truncation π r) P ∈ layerIdeal π r 1 := by
  rw [mem_layerIdeal_one_iff π hπ r hr, mapRingHom_derivative, hP, derivative_single]
  simp only [Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
  exact map_zero (HahnSeries.single _)

/-- The coefficient in degree `p-1` proves actual nonvanishing before any
normalization, using the original uniformizer factorization of `p`. -/
theorem derivative_ne_zero (p e : ℕ) (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) :
    derivative (Truncation π (e + 1)) P ≠ 0 := by
  have hpcoef : residue π hπ (e + 1) (by omega) (P.coeff (p : ℤ)) = 1 := by
    simpa only [mapRingHom_coeff, HahnSeries.coeff_single_same] using
      congrArg (fun X : LaurentSeries (IsLocalRing.ResidueField O) ↦ X.coeff (p : ℤ)) hP
  have hunit : IsUnit (P.coeff (p : ℤ)) :=
    isUnit_of_residue_ne_zero π hπ (e + 1) (by omega) _ (by rw [hpcoef]; exact one_ne_zero)
  have hpcast : (p : Truncation π (e + 1)) ≠ 0 := by
    have h := mk_pow_mul_unit_ne_zero π hπ e u hu
    rw [← hpe, map_natCast] at h
    exact h
  intro hzero
  have hc := congrArg (fun X : LaurentSeries (Truncation π (e + 1)) ↦ X.coeff ((p : ℤ) - 1)) hzero
  rw [coeff_derivative, sub_add_cancel, HahnSeries.coeff_zero, Int.cast_natCast] at hc
  exact hpcast (hunit.mul_left_eq_zero.mp hc)

/-- The actual finite Frobenius lift has a unique nonzero derivative layer
between one and `e`; nonvanishing is proved by its degree-`p-1` coefficient. -/
theorem exists_unique_derivative_layer (p e : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) :
    ∃! s : ℕ, 1 ≤ s ∧ s ≤ e ∧
      derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) s ∧
      derivative (Truncation π (e + 1)) P ∉ layerIdeal π (e + 1) (s + 1) := by
  simpa only [Nat.lt_succ_iff] using exists_unique_first_layer π (e + 1)
    (derivative (Truncation π (e + 1)) P)
    (derivative_ne_zero π hπ p e u hu hpe P hP)
    (derivative_mem_layerIdeal_one π hπ p (e + 1) (by omega) P hP)

/-- The unique actual first derivative layer of a finite Frobenius lift. -/
def derivativeLevel (p e : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) : ℕ :=
  Classical.choose (exists_unique_derivative_layer π hπ p e u hu hpe P hP)

/-- The chosen index has precisely the proved original first-layer properties. -/
theorem derivativeLevel_spec (p e : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) :
    let s := derivativeLevel π hπ p e u hu hpe P hP
    1 ≤ s ∧ s ≤ e ∧ derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) s ∧
      derivative (Truncation π (e + 1)) P ∉ layerIdeal π (e + 1) (s + 1) :=
  (Classical.choose_spec (exists_unique_derivative_layer π hπ p e u hu hpe P hP)).1

/-- The actual normalized derivative is obtained through the original graded
quotient, with its actual first layer supplied by the coefficient proof. -/
def normalizedDerivative (p e : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) :
    LaurentSeries (IsLocalRing.ResidueField O) :=
  let s := derivativeLevel π hπ p e u hu hpe P hP
  let hs := derivativeLevel_spec π hπ p e u hu hpe P hP
  layerResidue π hπ (e + 1) s (by omega) (derivative (Truncation π (e + 1)) P) hs.2.2.1

/-- The normalized derivative is nonzero in the actual residue Laurent field. -/
theorem normalizedDerivative_ne_zero (p e : ℕ) [CharP (IsLocalRing.ResidueField O) p]
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1) :
    normalizedDerivative π hπ p e u hu hpe P hP ≠ 0 :=
  (layerResidue_ne_zero_iff π hπ (e + 1) _ _ _ _).mpr
    (derivativeLevel_spec π hπ p e u hu hpe P hP).2.2.2

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem cast_factor_parameter (p e : ℕ) (u : O) (hpe : (p : O) = π ^ e * u) :
    (p : Truncation π (e + 1)) = parameter π (e + 1) ^ e * Ideal.Quotient.mk _ u := by
  simpa only [map_natCast, map_mul, map_pow, parameter] using
    congrArg (Ideal.Quotient.mk (Ideal.span {π ^ (e + 1)})) hpe

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem derivative_coeff_multiple (p e : ℕ)
    (P : LaurentSeries (Truncation π (e + 1))) (ℓ : ℤ) :
    (derivative (Truncation π (e + 1)) P).coeff ((p : ℤ) * ℓ - 1) =
      (p : Truncation π (e + 1)) * (ℓ : Truncation π (e + 1)) * P.coeff ((p : ℤ) * ℓ) := by
  rw [coeff_derivative, sub_add_cancel, Int.cast_mul, Int.cast_natCast]

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem derivative_coeff_mem_next_of_lt (p e : ℕ) (u : O)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (s : ℕ) (hs : s < e) (ℓ : ℤ) :
    (derivative (Truncation π (e + 1)) P).coeff ((p : ℤ) * ℓ - 1) ∈
      Ideal.span {parameter π (e + 1) ^ (s + 1)} := by
  rw [derivative_coeff_multiple, cast_factor_parameter π p e u hpe]
  apply span_pow_le (parameter π (e + 1)) (show s + 1 ≤ e by omega)
  apply Ideal.mem_span_singleton.mpr
  exact ⟨Ideal.Quotient.mk _ u * (ℓ : Truncation π (e + 1)) * P.coeff ((p : ℤ) * ℓ),
    by ring⟩

/-- Below the top coefficient level, the actual normalized derivative has an
actual Laurent primitive over the original residue field. -/
theorem normalizedDerivative_eq_derivative_of_lt (p e : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP < e) :
    ∃ A : LaurentSeries (IsLocalRing.ResidueField O),
      normalizedDerivative π hπ p e u hu hpe P hP = derivative (IsLocalRing.ResidueField O) A := by
  obtain ⟨A, hA⟩ := (exists_derivative_iff p (normalizedDerivative π hπ p e u hu hpe P hP)).mpr
    (by
      intro ℓ
      exact (layerResidue_coeff_eq_zero_iff π hπ (e + 1) _ _ _ _ _).mpr
        (derivative_coeff_mem_next_of_lt π p e u hpe P _ hs ℓ))
  exact ⟨A, hA.symm⟩

/-- At the top coefficient level, all forbidden derivative coefficients are
computed by the original residue of the unit factor of `p`. -/
theorem normalizedDerivative_coeff_multiple_of_eq (p e : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP = e) (ℓ : ℤ) :
    (normalizedDerivative π hπ p e u hu hpe P hP).coeff ((p : ℤ) * ℓ - 1) =
      IsLocalRing.residue O u * (ℓ : IsLocalRing.ResidueField O) *
        (HahnSeries.single (p : ℤ) (1 : IsLocalRing.ResidueField O)).coeff ((p : ℤ) * ℓ) := by
  let b : Truncation π (e + 1) := Ideal.Quotient.mk _ u * (ℓ : Truncation π (e + 1)) *
    P.coeff ((p : ℤ) * ℓ)
  have hb : (derivative (Truncation π (e + 1)) P).coeff ((p : ℤ) * ℓ - 1) =
      parameter π (e + 1) ^ derivativeLevel π hπ p e u hu hpe P hP * b := by
    rw [hs, derivative_coeff_multiple, cast_factor_parameter π p e u hpe]
    dsimp only [b]
    ring
  have hspec := derivativeLevel_spec π hπ p e u hu hpe P hP
  have hnorm := layerResidue_coeff_eq_of_coeff_eq π hπ (e + 1)
    (derivativeLevel π hπ p e u hu hpe P hP) (by omega)
    (derivative (Truncation π (e + 1)) P) hspec.2.2.1 ((p : ℤ) * ℓ - 1) b hb
  change (normalizedDerivative π hπ p e u hu hpe P hP).coeff ((p : ℤ) * ℓ - 1) =
    residue π hπ (e + 1) (by omega) b at hnorm
  refine hnorm.trans ?_
  have hc := congrArg
    (fun X : LaurentSeries (IsLocalRing.ResidueField O) ↦ X.coeff ((p : ℤ) * ℓ)) hP
  change residue π hπ (e + 1) (by omega) (P.coeff ((p : ℤ) * ℓ)) = _ at hc
  dsimp only [b]
  rw [map_mul, map_mul, residue_mk, map_intCast, hc]

/-- At the top coefficient level, the only nonintegrable term is the actual
residue of the unit factor of `p`, in degree `p - 1`. -/
theorem normalizedDerivative_eq_single_add_derivative_of_eq (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP = e) :
    ∃ A : LaurentSeries (IsLocalRing.ResidueField O),
      normalizedDerivative π hπ p e u hu hpe P hP =
        HahnSeries.single ((p : ℤ) - 1) (IsLocalRing.residue O u) +
          derivative (IsLocalRing.ResidueField O) A := by
  obtain ⟨A, hA⟩ := (exists_derivative_iff p
    (normalizedDerivative π hπ p e u hu hpe P hP -
      HahnSeries.single ((p : ℤ) - 1) (IsLocalRing.residue O u))).mpr (by
    intro ℓ
    rw [HahnSeries.coeff_sub, normalizedDerivative_coeff_multiple_of_eq π hπ p e u hu hpe P hP hs]
    by_cases hℓ : ℓ = 1
    · subst ℓ
      simp
    · have hp : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      have hm : (p : ℤ) * ℓ ≠ p := by
        intro h
        exact hℓ (mul_left_cancel₀ hp (by simpa using h))
      have hm' : (p : ℤ) * ℓ - 1 ≠ (p : ℤ) - 1 := by omega
      simp only [HahnSeries.coeff_single_of_ne hm, HahnSeries.coeff_single_of_ne hm',
        mul_zero, sub_zero])
  exact ⟨A, by rw [hA]; abel⟩

/-- The highest-layer normalized derivative has the actual coefficient `-c`
in its derivative, where `c` is the residue of the unit factor of `p`. -/
theorem derivative_normalizedDerivative_coeff_of_eq (p e : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP = e) :
    (derivative (IsLocalRing.ResidueField O)
      (normalizedDerivative π hπ p e u hu hpe P hP)).coeff ((p : ℤ) - 2) =
        -IsLocalRing.residue O u := by
  have hc := normalizedDerivative_coeff_multiple_of_eq π hπ p e u hu hpe P hP hs 1
  simp only [mul_one, Int.cast_one, HahnSeries.coeff_single_same] at hc
  rw [coeff_derivative, show (p : ℤ) - 2 + 1 = (p : ℤ) - 1 by omega, hc,
    Int.cast_sub, Int.cast_natCast, Int.cast_one, CharP.cast_eq_zero _ p,
    zero_sub, neg_one_mul]

/-- At the highest coefficient level the derivative is nonzero, and its
actual Laurent order is at most `p - 2`. -/
theorem derivative_normalizedDerivative_ne_zero_and_order_le_of_eq (p e : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel π hπ p e u hu hpe P hP = e) :
    let D := derivative (IsLocalRing.ResidueField O)
      (normalizedDerivative π hπ p e u hu hpe P hP)
    D ≠ 0 ∧ D.order ≤ (p : ℤ) - 2 := by
  dsimp only
  have hc : (derivative (IsLocalRing.ResidueField O)
      (normalizedDerivative π hπ p e u hu hpe P hP)).coeff ((p : ℤ) - 2) ≠ 0 := by
    rw [derivative_normalizedDerivative_coeff_of_eq π hπ p e u hu hpe P hP hs, neg_ne_zero]
    exact (hu.map (IsLocalRing.residue O)).ne_zero
  have hD := HahnSeries.ne_zero_of_coeff_ne_zero hc
  refine ⟨hD, ?_⟩
  exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hD).trans_le
    (HahnSeries.orderTop_le_of_coeff_ne_zero hc)

/-- Admissibility descends through the actual coefficient residue map. -/
theorem isAdmissible_residue (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G) :
    IsAdmissible (0 : IsLocalRing.ResidueField O) (mapRingHom (residue π hπ r hr) G) := by
  rw [isAdmissible_zero_iff]
  exact (isAdmissible_iff_actualResidue π hπ r hr G).mp hG

/-- Canonical finite substitution commutes with the original residue map, with
zero as the distinguished nilpotent in the actual residue field. -/
theorem residue_truncatedSubst (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (f : LaurentSeries (Truncation π r)) :
    mapRingHom (residue π hπ r hr) (truncatedSubst π hπ r hr G hG f) =
      subst 0 IsNilpotent.zero (mapRingHom (residue π hπ r hr) G)
        (isAdmissible_residue π hπ r hr G hG) (mapRingHom (residue π hπ r hr) f) := by
  let := parameter_isMaximal π hπ r hr
  obtain ⟨a, ha, horder⟩ := hG
  obtain ⟨U, Y, c, _, hdecomp, hUorder, hUunit, hc, hY⟩ :=
    exists_nilpotentLaurentEval_data (parameter π r) G r (parameter_pow_eq_zero π r) a horder
  let q := residue π hπ r hr
  let E := nilpotentLaurentEval (q (parameter π r)) (mapRingHom q U) (mapRingHom q Y)
    r hr (by simpa only [map_pow, map_zero] using congrArg q (parameter_pow_eq_zero π r)) a c ha hc
    (hUorder.ge.trans (orderTop_le_mapRingHom q U))
    (hY.trans (orderTop_le_mapRingHom q Y)) (hUunit.map (mapRingHom q))
  have hE : E = subst 0 IsNilpotent.zero (mapRingHom q G)
      (isAdmissible_residue π hπ r hr G ⟨a, ha, horder⟩) := by
    apply subst_unique _ _ _ _ E (continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _)
    change E (HahnSeries.single (1 : ℤ) 1) = mapRingHom q G
    rw [nilpotentLaurentEval_X, hdecomp, map_add, map_mul, mapRingHom_C]
  have hsource : truncatedSubst π hπ r hr G ⟨a, ha, horder⟩ =
      nilpotentLaurentEval (parameter π r) U Y r hr
        (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit :=
    subst_eq_nilpotentLaurentEval _ _ G ⟨a, ha, horder⟩ (parameter π r) U Y r hr
      (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit hdecomp
  exact (congrArg (fun F : LaurentSeries (Truncation π r) →ₐ[Truncation π r]
    LaurentSeries (Truncation π r) ↦ mapRingHom q (F f)) hsource).trans
    ((mapRingHom_nilpotentLaurentEval q _ U Y r hr
      (parameter_pow_eq_zero π r) a c ha hc hUorder.ge hY hUunit f).trans
      (congrArg (fun F : LaurentSeries (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O]
        LaurentSeries (IsLocalRing.ResidueField O) ↦ F (mapRingHom q f)) hE))

/-- Actual finite substitution preserves every original coefficient ideal. -/
theorem truncatedSubst_mem_layerIdeal (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (j : ℕ) (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j) :
    truncatedSubst π hπ r hr G hG X ∈ layerIdeal π r j := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  rw [hY, map_mul, map_pow, truncatedSubst_C]
  exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩

/-- The original graded-layer identification transports substitution to actual
substitution at the residue series. -/
theorem layerResidue_truncatedSubst (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (j : ℕ) (hjr : j < r) (X : LaurentSeries (Truncation π r))
    (hX : X ∈ layerIdeal π r j) :
    layerResidue π hπ r j hjr (truncatedSubst π hπ r hr G hG X)
        (truncatedSubst_mem_layerIdeal π hπ r hr G hG j X hX) =
      subst 0 IsNilpotent.zero (mapRingHom (residue π hπ r hr) G)
        (isAdmissible_residue π hπ r hr G hG) (layerResidue π hπ r j hjr X hX) := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  subst X
  simp only [map_mul, map_pow, truncatedSubst_C]
  rw [layerResidue_C_pow_mul, layerResidue_C_pow_mul]
  exact residue_truncatedSubst π hπ r hr G hG Y

/-- Multiplication in an actual coefficient layer reduces the other factor
through the original residue map. -/
theorem layerResidue_mul (r j : ℕ) (hjr : j < r)
    (X : LaurentSeries (Truncation π r)) (hX : X ∈ layerIdeal π r j)
    (Z : LaurentSeries (Truncation π r)) :
    layerResidue π hπ r j hjr (X * Z) ((layerIdeal π r j).mul_mem_right Z hX) =
      layerResidue π hπ r j hjr X hX * mapRingHom (residue π hπ r (by omega)) Z := by
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hX
  subst X
  simp only [mul_assoc]
  rw [layerResidue_C_pow_mul, layerResidue_C_pow_mul, map_mul]

/-- A finite Frobenius lift is admissible through its actual residue, without
an additional substitution-existence assumption. -/
theorem frobeniusLift_isAdmissible (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r))
    (hP : mapRingHom (residue π hπ r hr) P = HahnSeries.single (p : ℤ) 1) :
    IsAdmissible (parameter π r) P := by
  rw [isAdmissible_iff_actualResidue π hπ r hr P]
  refine ⟨p, by exact_mod_cast (Fact.out : p.Prime).pos, ?_⟩
  rw [hP, HahnSeries.orderTop_single one_ne_zero]

/-- Differentiating actual commuting substitutions and passing through the
original graded quotient gives the normalized derivative transformation law.
The actual prime-field equivalence supplies coefficientwise Frobenius. -/
theorem normalizedDerivative_commuting_substitution (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p]
    (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (G : LaurentSeries (Truncation π (e + 1)))
    (hG : IsAdmissible (parameter π (e + 1)) G)
    (hlinear : (mapRingHom (residue π hπ (e + 1) (by omega)) G).coeff 1 ≠ 0)
    (hcomm : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G hG P) :
    subst 0 IsNilpotent.zero (mapRingHom (residue π hπ (e + 1) (by omega)) G)
        (isAdmissible_residue π hπ (e + 1) (by omega) G hG)
        (normalizedDerivative π hπ p e u hu hpe P hP) =
      (derivative (IsLocalRing.ResidueField O)
        (mapRingHom (residue π hπ (e + 1) (by omega)) G)) ^ (p - 1) *
        normalizedDerivative π hπ p e u hu hpe P hP := by
  let := parameter_isMaximal π hπ (e + 1) (by omega)
  let q := residue π hπ (e + 1) (by omega)
  let s := derivativeLevel π hπ p e u hu hpe P hP
  have hspec := derivativeLevel_spec π hπ p e u hu hpe P hP
  have hs : s < e + 1 := by dsimp only [s]; omega
  have hDP : derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) s := hspec.2.2.1
  let FP := truncatedSubst π hπ (e + 1) (by omega) P
    (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP)
  let FG := truncatedSubst π hπ (e + 1) (by omega) G hG
  have hchain : derivative (Truncation π (e + 1)) P *
      FP (derivative (Truncation π (e + 1)) G) =
      FG (derivative (Truncation π (e + 1)) P) * derivative (Truncation π (e + 1)) G := by
    have hd := congrArg (derivative (Truncation π (e + 1))) hcomm
    have hFP := derivative_subst (parameter π (e + 1))
      ⟨e + 1, parameter_pow_eq_zero π (e + 1)⟩ P
      (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G
    have hFG := derivative_subst (parameter π (e + 1))
      ⟨e + 1, parameter_pow_eq_zero π (e + 1)⟩ G hG P
    exact (mul_comm _ _).trans (hFP.symm.trans (hd.trans hFG))
  have hFGDP : FG (derivative (Truncation π (e + 1)) P) ∈ layerIdeal π (e + 1) s :=
    truncatedSubst_mem_layerIdeal π hπ (e + 1) (by omega) G hG s _ hDP
  have hgraded : layerResidue π hπ (e + 1) s hs
      (derivative (Truncation π (e + 1)) P * FP (derivative (Truncation π (e + 1)) G))
      ((layerIdeal π (e + 1) s).mul_mem_right _ hDP) =
    layerResidue π hπ (e + 1) s hs
      (FG (derivative (Truncation π (e + 1)) P) * derivative (Truncation π (e + 1)) G)
      ((layerIdeal π (e + 1) s).mul_mem_right _ hFGDP) := by
    dsimp only [layerResidue]
    congr 2
    exact Subtype.ext hchain
  rw [layerResidue_mul π hπ (e + 1) s hs _ hDP _,
    layerResidue_mul π hπ (e + 1) s hs _ hFGDP _] at hgraded
  have hresP := residue_truncatedSubst π hπ (e + 1) (by omega) P
    (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP)
    (derivative (Truncation π (e + 1)) G)
  simp only [hP] at hresP
  rw [subst_primeMonomial_eq_pow p ε, mapRingHom_derivative] at hresP
  have hresG := layerResidue_truncatedSubst π hπ (e + 1) (by omega) G hG
    s hs (derivative (Truncation π (e + 1)) P) hDP
  rw [mapRingHom_derivative] at hgraded
  change normalizedDerivative π hπ p e u hu hpe P hP *
      mapRingHom q (FP (derivative (Truncation π (e + 1)) G)) =
    layerResidue π hπ (e + 1) s hs (FG (derivative (Truncation π (e + 1)) P)) hFGDP *
      derivative (IsLocalRing.ResidueField O) (mapRingHom q G) at hgraded
  rw [hresP, hresG] at hgraded
  change normalizedDerivative π hπ p e u hu hpe P hP *
      (derivative (IsLocalRing.ResidueField O) (mapRingHom q G)) ^ p =
    subst 0 IsNilpotent.zero (mapRingHom q G)
      (isAdmissible_residue π hπ (e + 1) (by omega) G hG)
      (normalizedDerivative π hπ p e u hu hpe P hP) *
      derivative (IsLocalRing.ResidueField O) (mapRingHom q G) at hgraded
  have hD : derivative (IsLocalRing.ResidueField O) (mapRingHom q G) ≠ 0 := by
    apply HahnSeries.ne_zero_of_coeff_ne_zero (g := 0)
    simpa only [coeff_derivative, zero_add, Int.cast_one, one_mul] using hlinear
  apply mul_right_cancel₀ hD
  rw [← hgraded]
  have hpow : (derivative (IsLocalRing.ResidueField O) (mapRingHom q G)) ^ p =
      (derivative (IsLocalRing.ResidueField O) (mapRingHom q G)) ^ (p - 1) *
        derivative (IsLocalRing.ResidueField O) (mapRingHom q G) := by
    have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
    simpa only [hp] using pow_succ
      (derivative (IsLocalRing.ResidueField O) (mapRingHom q G)) (p - 1)
  rw [hpow]
  ring

/-- The actual coordinate conjugate `H ∘ P ∘ H⁻¹`, using the already proved
canonical Laurent coordinate automorphism and its actual inverse. -/
def coordinateConjugate (r : ℕ) (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r)) (hP : IsAdmissible (parameter π r) P)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) : LaurentSeries (Truncation π r) := by
  let := parameter_isMaximal π hπ r hr
  exact (powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ H hzero hlinear).symm
    (truncatedSubst π hπ r hr P hP (HahnSeries.ofPowerSeries ℤ _ H))

/-- The defining actual coordinate-conjugacy identity on the original carrier. -/
theorem coordinateConjugate_identity (r : ℕ) (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r)) (hP : IsAdmissible (parameter π r) P)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    truncatedSubst π hπ r hr (HahnSeries.ofPowerSeries ℤ _ H)
      (by let := parameter_isMaximal π hπ r hr; exact isAdmissible_ofPowerSeries _ H hzero hlinear)
      (coordinateConjugate π hπ r hr P hP H hzero hlinear) =
      truncatedSubst π hπ r hr P hP (HahnSeries.ofPowerSeries ℤ _ H) := by
  let := parameter_isMaximal π hπ r hr
  exact (powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
    H hzero hlinear).apply_symm_apply _

/-- The actual power-series coordinate automorphism reduces coefficientwise
to the actual coordinate automorphism on the original residue field. -/
theorem residue_powerSeriesSubstEquiv (r : ℕ) (hr : 1 ≤ r)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (f : LaurentSeries (Truncation π r)) :
    mapRingHom (residue π hπ r hr)
      (by let := parameter_isMaximal π hπ r hr
          exact powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ H hzero hlinear f) =
      powerSeriesSubstEquiv (0 : IsLocalRing.ResidueField O) IsNilpotent.zero
        (H.map (residue π hπ r hr))
        (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, map_zero]
              using congrArg (residue π hπ r hr) hzero)
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr))
        (mapRingHom (residue π hπ r hr) f) := by
  let := parameter_isMaximal π hπ r hr
  change mapRingHom (residue π hπ r hr)
      (subst (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
        (HahnSeries.ofPowerSeries ℤ _ H) _ f) =
    subst 0 IsNilpotent.zero (HahnSeries.ofPowerSeries ℤ _ (H.map (residue π hπ r hr))) _
      (mapRingHom (residue π hπ r hr) f)
  simpa only [truncatedSubst, mapRingHom_ofPowerSeries] using
    residue_truncatedSubst π hπ r hr (HahnSeries.ofPowerSeries ℤ _ H)
      (isAdmissible_ofPowerSeries _ H hzero hlinear) f

/-- Actual coordinate conjugacy preserves the Frobenius residue over the
original prime residue field. No residue embedding is chosen in the coefficient ring. -/
theorem residue_coordinateConjugate (p r : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (hr : 1 ≤ r) (P : LaurentSeries (Truncation π r))
    (hP : mapRingHom (residue π hπ r hr) P = HahnSeries.single (p : ℤ) 1)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    mapRingHom (residue π hπ r hr)
      (coordinateConjugate π hπ r hr P (frobeniusLift_isAdmissible π hπ p r hr P hP)
        H hzero hlinear) = HahnSeries.single (p : ℤ) 1 := by
  let := parameter_isMaximal π hπ r hr
  let q := residue π hπ r hr
  let Hbar := H.map q
  have hz : Hbar.constantCoeff = 0 := by
    simpa only [Hbar, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, map_zero]
      using congrArg q hzero
  have hl : IsUnit (Hbar.coeff 1) := by
    simpa only [Hbar, PowerSeries.coeff_map] using hlinear.map q
  let E := powerSeriesSubstEquiv (0 : IsLocalRing.ResidueField O) IsNilpotent.zero Hbar hz hl
  let PH := coordinateConjugate π hπ r hr P (frobeniusLift_isAdmissible π hπ p r hr P hP)
    H hzero hlinear
  have hconj := coordinateConjugate_identity π hπ r hr P
    (frobeniusLift_isAdmissible π hπ p r hr P hP) H hzero hlinear
  have hnat := residue_powerSeriesSubstEquiv π hπ r hr H hzero hlinear PH
  have hres := residue_truncatedSubst π hπ r hr P
    (frobeniusLift_isAdmissible π hπ p r hr P hP) (HahnSeries.ofPowerSeries ℤ _ H)
  simp only [hP] at hres
  rw [subst_primeMonomial_eq_pow p ε] at hres
  have hX : E (HahnSeries.single (1 : ℤ) 1) = mapRingHom q (HahnSeries.ofPowerSeries ℤ _ H) := by
    simp only [E, powerSeriesSubstEquiv_apply, subst_X, Hbar, mapRingHom_ofPowerSeries]
  apply E.injective
  calc
    E (mapRingHom q PH) = mapRingHom q
        (truncatedSubst π hπ r hr (HahnSeries.ofPowerSeries ℤ _ H)
          (isAdmissible_ofPowerSeries _ H hzero hlinear) PH) := hnat.symm
    _ = mapRingHom q (truncatedSubst π hπ r hr P
        (frobeniusLift_isAdmissible π hπ p r hr P hP) (HahnSeries.ofPowerSeries ℤ _ H)) :=
      congrArg (mapRingHom q) hconj
    _ = (mapRingHom q (HahnSeries.ofPowerSeries ℤ _ H)) ^ p := hres
    _ = E (HahnSeries.single (p : ℤ) 1) := by
      rw [show (HahnSeries.single (p : ℤ) 1 : LaurentSeries (IsLocalRing.ResidueField O)) =
        (HahnSeries.single (1 : ℤ) 1) ^ p by simp [HahnSeries.single_pow], map_pow, hX]

/-- The actual derivative identity for coordinate conjugacy, before passing
to any coefficient layer. -/
theorem coordinateConjugate_derivative_identity (r : ℕ) (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r)) (hP : IsAdmissible (parameter π r) P)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    truncatedSubst π hπ r hr (HahnSeries.ofPowerSeries ℤ _ H)
        (by let := parameter_isMaximal π hπ r hr; exact isAdmissible_ofPowerSeries _ H hzero hlinear)
        (derivative (Truncation π r) (coordinateConjugate π hπ r hr P hP H hzero hlinear)) *
      derivative (Truncation π r) (HahnSeries.ofPowerSeries ℤ _ H) =
      truncatedSubst π hπ r hr P hP
        (derivative (Truncation π r) (HahnSeries.ofPowerSeries ℤ _ H)) *
          derivative (Truncation π r) P := by
  let := parameter_isMaximal π hπ r hr
  have hd := congrArg (derivative (Truncation π r))
    (coordinateConjugate_identity π hπ r hr P hP H hzero hlinear)
  have hleft := derivative_subst (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
    (HahnSeries.ofPowerSeries ℤ _ H) (isAdmissible_ofPowerSeries _ H hzero hlinear)
    (coordinateConjugate π hπ r hr P hP H hzero hlinear)
  have hright := derivative_subst (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
    P hP (HahnSeries.ofPowerSeries ℤ _ H)
  exact hleft.symm.trans (hd.trans hright)

/-- Actual coordinate conjugacy preserves membership of the derivative in
every original coefficient layer. Both derivative factors are actual units. -/
theorem coordinateConjugate_derivative_mem_iff (r : ℕ) (hr : 1 ≤ r)
    (P : LaurentSeries (Truncation π r)) (hP : IsAdmissible (parameter π r) P)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (j : ℕ) :
    derivative (Truncation π r) (coordinateConjugate π hπ r hr P hP H hzero hlinear) ∈
      layerIdeal π r j ↔ derivative (Truncation π r) P ∈ layerIdeal π r j := by
  let := parameter_isMaximal π hπ r hr
  let E := powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ H hzero hlinear
  let PH := coordinateConjugate π hπ r hr P hP H hzero hlinear
  let DH := derivative (Truncation π r) (HahnSeries.ofPowerSeries ℤ _ H)
  let FP := truncatedSubst π hπ r hr P hP
  have hDH : IsUnit DH := isUnit_derivative_ofPowerSeries H hlinear
  have hFPDH : IsUnit (FP DH) := hDH.map FP
  have hchain : E (derivative (Truncation π r) PH) * DH =
      FP DH * derivative (Truncation π r) P :=
    coordinateConjugate_derivative_identity π hπ r hr P hP H hzero hlinear
  calc
    derivative (Truncation π r) PH ∈ layerIdeal π r j ↔
        E (derivative (Truncation π r) PH) ∈ layerIdeal π r j :=
      (algEquiv_mem_layerIdeal_iff π r E j _).symm
    _ ↔ E (derivative (Truncation π r) PH) * DH ∈ layerIdeal π r j :=
      ((layerIdeal π r j).mul_unit_mem_iff_mem hDH).symm
    _ ↔ FP DH * derivative (Truncation π r) P ∈ layerIdeal π r j := by rw [hchain]
    _ ↔ derivative (Truncation π r) P ∈ layerIdeal π r j :=
      (layerIdeal π r j).unit_mul_mem_iff_mem hFPDH

/-- The actual first nonzero derivative level is invariant under the actual
power-series coordinate conjugacy. -/
theorem derivativeLevel_coordinateConjugate (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (H : PowerSeries (Truncation π (e + 1))) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    derivativeLevel π hπ p e u hu hpe
      (coordinateConjugate π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) H hzero hlinear)
      (residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear) =
        derivativeLevel π hπ p e u hu hpe P hP := by
  have hs := derivativeLevel_spec π hπ p e u hu hpe P hP
  have hi := coordinateConjugate_derivative_mem_iff π hπ (e + 1) (by omega) P
    (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) H hzero hlinear
  apply Eq.symm
  apply (Classical.choose_spec (exists_unique_derivative_layer π hπ p e u hu hpe
    _ (residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear))).2
  exact ⟨hs.1, hs.2.1, (hi _).mpr hs.2.2.1, fun h ↦ hs.2.2.2 ((hi _).mp h)⟩

/-- Computing a known actual derivative level uses exactly the original
graded quotient at that level. -/
theorem normalizedDerivative_eq_layerResidue (p e : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (u : O) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (j : ℕ) (hjr : j < e + 1) (hj : derivativeLevel π hπ p e u hu hpe P hP = j)
    (hmem : derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) j) :
    normalizedDerivative π hπ p e u hu hpe P hP =
      layerResidue π hπ (e + 1) j hjr (derivative (Truncation π (e + 1)) P) hmem := by
  subst j
  rfl

/-- The normalized derivative transforms under the actual coordinate conjugacy
by the `(p - 1)`st power of the residue-coordinate derivative. -/
theorem normalizedDerivative_coordinateConjugate (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (H : PowerSeries (Truncation π (e + 1))) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    let PH := coordinateConjugate π hπ (e + 1) (by omega) P
      (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) H hzero hlinear
    let hPH := residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear
    subst 0 IsNilpotent.zero
        (mapRingHom (residue π hπ (e + 1) (by omega)) (HahnSeries.ofPowerSeries ℤ _ H))
        (isAdmissible_residue π hπ (e + 1) (by omega) _
          (by let := parameter_isMaximal π hπ (e + 1) (by omega)
              exact isAdmissible_ofPowerSeries _ H hzero hlinear))
        (normalizedDerivative π hπ p e u hu hpe PH hPH) =
      (derivative (IsLocalRing.ResidueField O)
        (mapRingHom (residue π hπ (e + 1) (by omega)) (HahnSeries.ofPowerSeries ℤ _ H))) ^ (p - 1) *
        normalizedDerivative π hπ p e u hu hpe P hP := by
  dsimp only
  let := parameter_isMaximal π hπ (e + 1) (by omega)
  let q := residue π hπ (e + 1) (by omega)
  let hadmP := frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP
  let PH := coordinateConjugate π hπ (e + 1) (by omega) P hadmP H hzero hlinear
  have hPH := residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear
  let s := derivativeLevel π hπ p e u hu hpe P hP
  have hspec := derivativeLevel_spec π hπ p e u hu hpe P hP
  have hs : s < e + 1 := by dsimp only [s]; omega
  have hDP : derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) s := hspec.2.2.1
  have hDPH : derivative (Truncation π (e + 1)) PH ∈ layerIdeal π (e + 1) s :=
    (coordinateConjugate_derivative_mem_iff π hπ (e + 1) (by omega) P hadmP H hzero hlinear s).mpr hDP
  let HL := HahnSeries.ofPowerSeries ℤ (Truncation π (e + 1)) H
  let hadmH := isAdmissible_ofPowerSeries (parameter π (e + 1)) H hzero hlinear
  let FH := truncatedSubst π hπ (e + 1) (by omega) HL hadmH
  let FP := truncatedSubst π hπ (e + 1) (by omega) P hadmP
  have hFHDPH : FH (derivative (Truncation π (e + 1)) PH) ∈ layerIdeal π (e + 1) s :=
    truncatedSubst_mem_layerIdeal π hπ (e + 1) (by omega) HL hadmH s _ hDPH
  have hchain : FH (derivative (Truncation π (e + 1)) PH) * derivative (Truncation π (e + 1)) HL =
      derivative (Truncation π (e + 1)) P * FP (derivative (Truncation π (e + 1)) HL) :=
    (coordinateConjugate_derivative_identity π hπ (e + 1) (by omega) P hadmP H hzero hlinear).trans
      (mul_comm _ _)
  have hg := congrArg (fun x : layerSubmodule π (e + 1) s ↦
      (gradedLayerEquiv π hπ (e + 1) s hs).symm (Submodule.Quotient.mk x))
    (Subtype.ext hchain :
      (⟨_, (layerIdeal π (e + 1) s).mul_mem_right _ hFHDPH⟩ : layerSubmodule π (e + 1) s) =
      ⟨_, (layerIdeal π (e + 1) s).mul_mem_right _ hDP⟩)
  change layerResidue π hπ (e + 1) s hs _ _ = layerResidue π hπ (e + 1) s hs _ _ at hg
  rw [layerResidue_mul π hπ (e + 1) s hs _ hFHDPH _,
    layerResidue_mul π hπ (e + 1) s hs _ hDP _] at hg
  have hleft := layerResidue_truncatedSubst π hπ (e + 1) (by omega) HL hadmH s hs _ hDPH
  have hform := normalizedDerivative_eq_layerResidue π hπ p e u hu hpe PH hPH s hs
    (derivativeLevel_coordinateConjugate π hπ p e ε u hu hpe P hP H hzero hlinear) hDPH
  have hright := residue_truncatedSubst π hπ (e + 1) (by omega) P hadmP
    (derivative (Truncation π (e + 1)) HL)
  simp only [hP] at hright
  rw [subst_primeMonomial_eq_pow p ε, mapRingHom_derivative] at hright
  rw [hleft, ← hform, hright, mapRingHom_derivative] at hg
  change subst 0 IsNilpotent.zero (mapRingHom q HL)
        (isAdmissible_residue π hπ (e + 1) (by omega) HL hadmH)
        (normalizedDerivative π hπ p e u hu hpe PH hPH) *
      derivative (IsLocalRing.ResidueField O) (mapRingHom q HL) =
    normalizedDerivative π hπ p e u hu hpe P hP *
      (derivative (IsLocalRing.ResidueField O) (mapRingHom q HL)) ^ p at hg
  have hD : derivative (IsLocalRing.ResidueField O) (mapRingHom q HL) ≠ 0 := by
    rw [← mapRingHom_derivative]
    exact ((isUnit_derivative_ofPowerSeries H hlinear).map (mapRingHom q)).ne_zero
  apply mul_right_cancel₀ hD
  rw [hg]
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
  have hpow := pow_succ (derivative (IsLocalRing.ResidueField O) (mapRingHom q HL)) (p - 1)
  rw [hp] at hpow
  rw [hpow]
  ring

/-- The normalized derivative has invariant actual Laurent order under the
canonical power-series coordinate conjugacy. -/
theorem order_normalizedDerivative_coordinateConjugate (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (H : PowerSeries (Truncation π (e + 1))) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    let PH := coordinateConjugate π hπ (e + 1) (by omega) P
      (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) H hzero hlinear
    let hPH := residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear
    (normalizedDerivative π hπ p e u hu hpe PH hPH).order =
      (normalizedDerivative π hπ p e u hu hpe P hP).order := by
  dsimp only
  let q := residue π hπ (e + 1) (by omega)
  let Hbar := H.map q
  have hz : Hbar.constantCoeff = 0 := by
    simpa only [Hbar, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, map_zero]
      using congrArg q hzero
  have hl : IsUnit (Hbar.coeff 1) := by
    simpa only [Hbar, PowerSeries.coeff_map] using hlinear.map q
  let PH := coordinateConjugate π hπ (e + 1) (by omega) P
    (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) H hzero hlinear
  have hPH := residue_coordinateConjugate π hπ p (e + 1) ε (by omega) P hP H hzero hlinear
  let NP := normalizedDerivative π hπ p e u hu hpe P hP
  let NH := normalizedDerivative π hπ p e u hu hpe PH hPH
  let DH := derivative (IsLocalRing.ResidueField O)
    (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) Hbar)
  have ht := normalizedDerivative_coordinateConjugate π hπ p e ε u hu hpe P hP H hzero hlinear
  dsimp only at ht
  simp only [mapRingHom_ofPowerSeries] at ht
  change powerSeriesSubstEquiv 0 IsNilpotent.zero Hbar hz hl NH = DH ^ (p - 1) * NP at ht
  have hDH : DH ≠ 0 := (isUnit_derivative_ofPowerSeries Hbar hl).ne_zero
  calc
    NH.order = (powerSeriesSubstEquiv 0 IsNilpotent.zero Hbar hz hl NH).order :=
      (order_powerSeriesSubstEquiv Hbar hz hl NH).symm
    _ = (DH ^ (p - 1) * NP).order := congrArg HahnSeries.order ht
    _ = (DH ^ (p - 1)).order + NP.order :=
      HahnSeries.order_mul (pow_ne_zero _ hDH) (normalizedDerivative_ne_zero π hπ p e u hu hpe P hP)
    _ = NP.order := by
      rw [order_pow_of_order_zero DH hDH (order_derivative_ofPowerSeries Hbar hl), zero_add]

end DiscreteValuationRing

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
  [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F
local notation "O_0" => Valuation.valuationSubring (NormedField.valuation (K := Padic p))

/-- Total ramification identifies the original spectral residue field with
the prime field, using the original residue algebra map. -/
def coefficientExtensionPrimeResidueEquiv
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) : IsLocalRing.ResidueField O_F ≃+* ZMod p := by
  have hdeg := FontaineWintenberger.extensionValuationSubring_ramificationIdx_mul_residueDegree
    (Padic p) F (FontaineWintenberger.spectralValuation (Padic p) F)
  have hpos := FontaineWintenberger.local_ramificationIdx_pos O_0 O_F
  have hf : Module.finrank (IsLocalRing.ResidueField O_0) (IsLocalRing.ResidueField O_F) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    simpa only [mul_one] using hdeg.trans htotal.symm
  have hbij : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField O_0) (IsLocalRing.ResidueField O_F)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf
  exact (RingEquiv.ofBijective _ hbij).symm.trans
    ((IsLocalRing.ResidueField.mapEquiv (FalseTateExtension.padicUnitBallEquiv p)).trans
      (PadicInt.residueField (p := p)))

/-- The actual spectral residue has characteristic `p`, derived from total
ramification rather than imposed as an extra coefficient-field structure. -/
theorem coefficientExtensionResidue_charP
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) : CharP (IsLocalRing.ResidueField O_F) p :=
  ((coefficientExtensionPrimeResidueEquiv p F htotal).toRingHom.charP_iff_charP p).mpr inferInstance

/-- In the actual spectral integer ring, a uniformizer decomposes `p` with a
unit factor, and the exponent is its actual normalized additive valuation. -/
theorem coefficientExtension_exists_p_factor (π : O_F) (hπ : Irreducible π) :
    ∃ (e : ℕ) (u : O_Fˣ), (p : O_F) = π ^ e * u ∧
      IsDiscreteValuationRing.addVal O_F (p : O_F) = e := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap (Padic p) F).injective
  have hp : (p : O_F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨e, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp hπ
  exact ⟨e, u, hpu.trans (mul_comm _ _), IsDiscreteValuationRing.addVal_def _ u hπ e hpu⟩

/-- The actual finite coefficient extension has the asserted unique nonzero
derivative layer at truncation `vπ(p) + 1`. All residue and unit-factor data
are constructed from the original spectral integers and total ramification. -/
theorem coefficientExtension_exists_unique_derivative_layer
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) (π : O_F) (hπ : Irreducible π) :
    ∃ (e : ℕ), IsDiscreteValuationRing.addVal O_F (p : O_F) = e ∧
      ∀ P : LaurentSeries (Truncation π (e + 1)),
        mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1 →
        ∃! s : ℕ, 1 ≤ s ∧ s ≤ e ∧
          derivative (Truncation π (e + 1)) P ∈ layerIdeal π (e + 1) s ∧
          derivative (Truncation π (e + 1)) P ∉ layerIdeal π (e + 1) (s + 1) := by
  let := coefficientExtensionResidue_charP p F htotal
  obtain ⟨e, u, hpe, he⟩ := coefficientExtension_exists_p_factor p F π hπ
  refine ⟨e, he, ?_⟩
  intro P hP
  exact exists_unique_derivative_layer π hπ p e u u.isUnit hpe P hP

local instance coefficientResidueZeroSpanIsMaximal :
    (Ideal.span ({(0 : IsLocalRing.ResidueField O_F)} : Set (IsLocalRing.ResidueField O_F))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The normalized commuting chain law for the actual finite totally ramified
coefficient extension. Its prime residue identification and characteristic
come from the actual total-ramification theorem, with no residue-field assumption. -/
theorem coefficientExtension_normalizedDerivative_commuting_substitution
    (htotal : (IsLocalRing.maximalIdeal O_F).ramificationIdx O_0 =
      Module.finrank (Padic p) F) (π : O_F) (hπ : Irreducible π)
    (e : ℕ) (u : O_F) (hu : IsUnit u) (hpe : (p : O_F) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (G : LaurentSeries (Truncation π (e + 1)))
    (hG : IsAdmissible (parameter π (e + 1)) G)
    (hlinear : (mapRingHom (residue π hπ (e + 1) (by omega)) G).coeff 1 ≠ 0)
    (hcomm : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G hG P) :
    let : CharP (IsLocalRing.ResidueField O_F) p := coefficientExtensionResidue_charP p F htotal
    subst 0 IsNilpotent.zero (mapRingHom (residue π hπ (e + 1) (by omega)) G)
        (isAdmissible_residue π hπ (e + 1) (by omega) G hG)
        (normalizedDerivative π hπ p e u hu hpe P hP) =
      (derivative (IsLocalRing.ResidueField O_F)
        (mapRingHom (residue π hπ (e + 1) (by omega)) G)) ^ (p - 1) *
        normalizedDerivative π hπ p e u hu hpe P hP := by
  let := coefficientExtensionResidue_charP p F htotal
  exact normalizedDerivative_commuting_substitution π hπ p e
    (coefficientExtensionPrimeResidueEquiv p F htotal) u hu hpe P hP G hG hlinear hcomm

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing
