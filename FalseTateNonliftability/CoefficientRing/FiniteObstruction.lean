module

public import FalseTateNonliftability.CoefficientRing.TopLevelObstruction
public import FalseTateNonliftability.LaurentSeries.InvariantExactDifferential
public import FalseTateNonliftability.LaurentSeries.ExactDifferentialLimit
public import FalseTateExtension.Padic.KummerRamification

/-!
# A numerical finite-precision obstruction

Actual finite commuting substitutions are excluded by the original normalized
derivative, an actual exact invariant differential, and the prescribed p-adic
ramification limit. This is the numerical criterion in Yuan, Section 6;
identifying the actual false Tate action and its ramification data is separate.
-/

@[expose] public section

noncomputable section

open Filter Topology LaurentSeries
open scoped Topology

namespace FalseTateNonliftability.CoefficientRing

/-- The actual integral p-adic ramification limit is not an integer. This uses
integer injectivity, without any order structure on the p-adic field. -/
theorem kummerRamificationLimit_ne_intCast (p : ℕ) [Fact p.Prime] (z : ℤ) :
    FalseTateExtension.kummerRamificationLimit p ≠ (z : PadicInt p) := by
  intro heq
  have hmul : FalseTateExtension.kummerRamificationLimit p *
      ((p : PadicInt p) + 1) = (p : PadicInt p) - 1 := by
    change (((p : PadicInt p) - 1) *
      ↑((FalseTateExtension.kummerRamificationDenominator p)⁻¹)) *
      ((p : PadicInt p) + 1) = (p : PadicInt p) - 1
    rw [← FalseTateExtension.coe_kummerRamificationDenominator, mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [heq] at hmul
  have hz : z * ((p : ℤ) + 1) = (p : ℤ) - 1 := by exact_mod_cast hmul
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hpos : 0 < z := by nlinarith
  have hlt : z < 1 := by nlinarith
  omega

local instance finiteObstructionZeroSpanIsMaximal {k : Type*} [Field k] :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual numerical limit excludes both weighted identities for a
nonzero exact Laurent series over the original prime field. -/
theorem not_weighted_exact_of_ramification_limit (p : ℕ) [Fact p.Prime]
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (hlinear ▸ isUnit_one)))
    (hlimit : Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ (ZMod p) (powerSeriesIterate f (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
      (nhds (FalseTateExtension.kummerRamificationLimit p)))
    (g : PowerSeries (ZMod p)) (hg : g.constantCoeff = 0)
    (ell : (ZMod p)ˣ) (hell : g.coeff 1 = (ell : ZMod p))
    (horder : orderOf ell = p - 1)
    (h A : LaurentSeries (ZMod p)) (hne : h ≠ 0) (hA : derivative (ZMod p) A = h)
    (hfweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
        (hlinear ▸ isUnit_one) h =
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) f) ^ (p - 1) * h)
    (hgweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg
        (hell.symm ▸ ell.isUnit) h =
      derivative (ZMod p) (HahnSeries.ofPowerSeries ℤ (ZMod p) g) ^ (p - 1) * h) : False := by
  obtain ⟨a, B, ha, hB, hinv⟩ := exists_exact_invariant_of_weighted_identities p
    f hf hlinear g hg ell hell horder h A hne hA hfweighted hgweighted
  have hvalue := padic_ramification_limit_eq_of_invariant_exact_differential p f hf hlinear
    hinfinite (FalseTateExtension.kummerRamificationLimit p) hlimit a ha ⟨B, hB⟩ hinv
  apply kummerRamificationLimit_ne_intCast p (-(a.order + 1))
  simpa only [Int.cast_neg] using hvalue

private theorem coefficient_map_injective {k K : Type*} [CommRing k] [CommRing K]
    (ψ : k →+* K) (hψ : Function.Injective ψ) : Function.Injective (mapRingHom ψ) := by
  intro x y hxy
  ext j
  apply hψ
  exact congrArg (fun z : LaurentSeries K ↦ z.coeff j) hxy

theorem order_coefficient_map {k K : Type*} [CommRing k] [CommRing K]
    (ψ : k →+* K) (hψ : Function.Injective ψ) (x : LaurentSeries k) :
    (mapRingHom ψ x).order = x.order := by
  by_cases hx : x = 0
  · simp [hx]
  have hm : mapRingHom ψ x ≠ 0 := by
    intro hz
    apply hx
    apply coefficient_map_injective ψ hψ
    simpa only [map_zero] using hz
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero hm,
    orderTop_mapRingHom_of_injective ψ hψ, ← HahnSeries.order_eq_orderTop_of_ne_zero hx]

theorem coefficient_map_coordinate {k K : Type*} [Field k] [Field K]
    (ψ : k →+* K) (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hlinear : IsUnit (g.coeff 1)) (x : LaurentSeries k) :
    mapRingHom ψ (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear x) =
      powerSeriesSubstEquiv 0 IsNilpotent.zero (g.map ψ)
        (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_map, map_zero] using congrArg ψ hg)
        (by simpa only [PowerSeries.coeff_map] using hlinear.map ψ)
        (mapRingHom ψ x) := by
  let U := HahnSeries.ofPowerSeries ℤ k g
  have hU : IsAdmissible (0 : k) U := isAdmissible_ofPowerSeries 0 g hg hlinear
  have hbound : (1 : WithTop ℤ) ≤ U.orderTop := ofPowerSeries_mem_orderAddSubgroup_one g hg
  have hunit : IsUnit U := hU.isUnit 0 IsNilpotent.zero
  have hs := subst_eq_nilpotentLaurentEval (0 : k) IsNilpotent.zero U hU
    0 U 0 1 (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) hunit (by simp)
  have hz : PowerSeries.constantCoeff (g.map ψ) = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, map_zero] using congrArg ψ hg
  have hl : IsUnit ((g.map ψ).coeff 1) := by
    simpa only [PowerSeries.coeff_map] using hlinear.map ψ
  have ht := subst_eq_nilpotentLaurentEval (0 : K) IsNilpotent.zero
    (HahnSeries.ofPowerSeries ℤ K (g.map ψ)) (isAdmissible_ofPowerSeries 0 _ hz hl)
    (ψ 0) (mapRingHom ψ U) (mapRingHom ψ (0 : LaurentSeries k)) 1
    (by omega) (by simp) 1 0 (by omega) le_rfl
    (le_trans hbound (orderTop_le_mapRingHom ψ U))
    (by simp) (hunit.map (mapRingHom ψ)) (by simp [U, mapRingHom_ofPowerSeries])
  have hmap := mapRingHom_nilpotentLaurentEval ψ (0 : k) U 0 1 (by omega)
    (by simp) 1 0 (by omega) le_rfl hbound (by simp) hunit x
  rw [← hs, ← ht] at hmap
  simpa only [powerSeriesSubstEquiv_apply] using hmap

theorem coefficient_map_iterate_variable {k K : Type*} [Field k] [Field K]
    (ψ : k →+* K) (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hlinear : IsUnit (g.coeff 1)) (n : ℕ) :
    mapRingHom ψ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate g n)) =
      HahnSeries.ofPowerSeries ℤ K (powerSeriesIterate (g.map ψ) n) := by
  have hz : PowerSeries.constantCoeff (g.map ψ) = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, map_zero] using congrArg ψ hg
  have hl : IsUnit ((g.map ψ).coeff 1) := by
    simpa only [PowerSeries.coeff_map] using hlinear.map ψ
  have hs : Function.Semiconj (mapRingHom ψ)
      (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear)
      (powerSeriesSubstEquiv 0 IsNilpotent.zero (g.map ψ) hz hl) :=
    fun x ↦ coefficient_map_coordinate ψ g hg hlinear x
  have hi := hs.iterate_right n (HahnSeries.single (1 : ℤ) 1)
  rw [← ofPowerSeries_powerSeriesIterate g hg hlinear n,
    mapRingHom_single, map_one, ← ofPowerSeries_powerSeriesIterate (g.map ψ) hz hl n] at hi
  exact hi

theorem order_mapped_iterate_displacement {k K : Type*} [Field k] [Field K]
    (ψ : k →+* K) (hψ : Function.Injective ψ) (g : PowerSeries k)
    (hg : g.constantCoeff = 0) (hlinear : IsUnit (g.coeff 1)) (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K (powerSeriesIterate (g.map ψ) n) -
      HahnSeries.single (1 : ℤ) 1).order =
      (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate g n) -
        HahnSeries.single (1 : ℤ) 1).order := by
  have hm : mapRingHom ψ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate g n) -
      HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.ofPowerSeries ℤ K (powerSeriesIterate (g.map ψ) n) -
        HahnSeries.single (1 : ℤ) 1 := by
    rw [map_sub, coefficient_map_iterate_variable ψ g hg hlinear n,
      mapRingHom_single, map_one]
  exact (congrArg HahnSeries.order hm).symm.trans
    (order_coefficient_map ψ hψ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate g n) -
      HahnSeries.single (1 : ℤ) 1))

theorem infinite_order_mapped_coordinate {k K : Type*} [Field k] [Field K]
    (ψ : k →+* K) (hψ : Function.Injective ψ) (g : PowerSeries k)
    (hg : g.constantCoeff = 0) (hlinear : IsUnit (g.coeff 1))
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear)) :
    ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero (g.map ψ)
      (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_map, map_zero] using congrArg ψ hg)
      (by simpa only [PowerSeries.coeff_map] using hlinear.map ψ)) := by
  intro hfinite
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear
  let F := powerSeriesSubstEquiv (0 : K) IsNilpotent.zero (g.map ψ)
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map, map_zero] using congrArg ψ hg)
    (by simpa only [PowerSeries.coeff_map] using hlinear.map ψ)
  have hs : Function.Semiconj (mapRingHom ψ) E F :=
    fun x ↦ coefficient_map_coordinate ψ g hg hlinear x
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfinite
  apply hinfinite
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  change E ^ n = 1
  apply AlgEquiv.ext
  intro x
  change (E ^ n) x = x
  apply coefficient_map_injective ψ hψ
  calc
    mapRingHom ψ ((E ^ n) x) = (F ^ n) (mapRingHom ψ x) := by
      simpa only [AlgEquiv.coe_pow] using hs.iterate_right n x
    _ = mapRingHom ψ x := by rw [hpow]; rfl

theorem order_units_coefficient_map {k K : Type*} [CommRing k] [CommRing K]
    (ψ : k →+* K) (hψ : Function.Injective ψ) (ell : kˣ) :
    orderOf (Units.map ψ.toMonoidHom ell) = orderOf ell := by
  apply orderOf_injective (Units.map ψ.toMonoidHom)
  intro x y hxy
  apply Units.val_injective
  apply hψ
  exact congrArg Units.val hxy

private theorem coefficient_map_weighted {k K : Type*} [Field k] [Field K]
    (ψ : k →+* K) (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hlinear : IsUnit (g.coeff 1)) (n : ℕ) (h : LaurentSeries k)
    (hweighted : powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear h =
      derivative k (HahnSeries.ofPowerSeries ℤ k g) ^ n * h) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero (g.map ψ)
        (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_map, map_zero] using congrArg ψ hg)
        (by simpa only [PowerSeries.coeff_map] using hlinear.map ψ)
        (mapRingHom ψ h) =
      derivative K (HahnSeries.ofPowerSeries ℤ K (g.map ψ)) ^ n * mapRingHom ψ h := by
  have hm := congrArg (mapRingHom ψ) hweighted
  rw [coefficient_map_coordinate, map_mul, map_pow, mapRingHom_derivative,
    mapRingHom_ofPowerSeries] at hm
  exact hm

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π)

/-- The actual commuting finite substitutions give the weighted identity for
the original residue power-series coordinate. Its admissibility is derived. -/
theorem normalizedDerivative_weighted_powerSeries (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (G : LaurentSeries (Truncation π (e + 1)))
    (g : PowerSeries (IsLocalRing.ResidueField O)) (hg : g.constantCoeff = 0)
    (hlinear : IsUnit (g.coeff 1))
    (hres : mapRingHom (residue π hπ (e + 1) (by omega)) G = HahnSeries.ofPowerSeries ℤ _ g)
    (hcomm : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G
        (isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) G g hg hlinear hres) P) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero g hg hlinear
        (normalizedDerivative π hπ p e u hu hpe P hP) =
      derivative (IsLocalRing.ResidueField O) (HahnSeries.ofPowerSeries ℤ _ g) ^ (p - 1) *
        normalizedDerivative π hπ p e u hu hpe P hP := by
  let hG := isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) G g hg hlinear hres
  have hl : (mapRingHom (residue π hπ (e + 1) (by omega)) G).coeff 1 ≠ 0 := by
    rw [hres]
    simpa only [show (1 : ℤ) = (1 : ℕ) from rfl, HahnSeries.ofPowerSeries_apply_coeff]
      using hlinear.ne_zero
  have hweighted := normalizedDerivative_commuting_substitution π hπ p e ε u hu hpe
    P hP G hG hl hcomm
  rw [residue_substitution_eq_powerSeriesSubstEquiv π hπ (e + 1) (by omega)
    G hG g hg hlinear hres, hres] at hweighted
  exact hweighted

/-- **The numerical finite obstruction.** The original finite Frobenius lift
cannot commute with both prescribed residue coordinates when their actual
iteration data have the stated congruence, growth and p-adic limit. The
normalized derivative, primitive and exact invariant differential are proved
producers, rather than additional hypotheses. -/
theorem not_commuting_finite_lifts_of_numerical_ramification (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (ε : IsLocalRing.ResidueField O ≃+* ZMod p)
    (u : O) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    (P : LaurentSeries (Truncation π (e + 1)))
    (hP : mapRingHom (residue π hπ (e + 1) (by omega)) P = HahnSeries.single (p : ℤ) 1)
    (G D : LaurentSeries (Truncation π (e + 1)))
    (f g : PowerSeries (IsLocalRing.ResidueField O))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (hg : g.constantCoeff = 0)
    (ell : (IsLocalRing.ResidueField O)ˣ) (hell : g.coeff 1 = (ell : IsLocalRing.ResidueField O))
    (horder : orderOf ell = p - 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (hlinear ▸ isUnit_one)))
    (hresG : mapRingHom (residue π hπ (e + 1) (by omega)) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hresD : mapRingHom (residue π hπ (e + 1) (by omega)) D = HahnSeries.ofPowerSeries ℤ _ g)
    (hdiv : ∀ n : ℕ, (p : ℤ) ∣
      ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1) + 1)
    (hfast : ∀ n : ℕ, ((p : ℤ) + 1) *
        ((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) -
          HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ (n + 1))) -
        HahnSeries.single (1 : ℤ) 1).order - 1)
    (hlimit : Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ _ (powerSeriesIterate f (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
      (nhds (FalseTateExtension.kummerRamificationLimit p)))
    (hcommG : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) G =
      truncatedSubst π hπ (e + 1) (by omega) G
        (isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) G f hf
          (hlinear ▸ isUnit_one) hresG) P)
    (hcommD : truncatedSubst π hπ (e + 1) (by omega) P
        (frobeniusLift_isAdmissible π hπ p (e + 1) (by omega) P hP) D =
      truncatedSubst π hπ (e + 1) (by omega) D
        (isAdmissible_of_residue_powerSeries π hπ (e + 1) (by omega) D g hg
          (hell.symm ▸ ell.isUnit) hresD) P) : False := by
  have hs := derivativeLevel_lt_of_iterate_growth π hπ p e ε u hu hpe P hP G f hf hlinear
    hinfinite hresG hdiv hfast hcommG
  let h := normalizedDerivative π hπ p e u hu hpe P hP
  have hne : h ≠ 0 := normalizedDerivative_ne_zero π hπ p e u hu hpe P hP
  obtain ⟨A, hA⟩ := normalizedDerivative_eq_derivative_of_lt π hπ p e u hu hpe P hP hs
  have hwf := normalizedDerivative_weighted_powerSeries π hπ p e ε u hu hpe P hP G f hf
    (hlinear ▸ isUnit_one) hresG hcommG
  have hwg := normalizedDerivative_weighted_powerSeries π hπ p e ε u hu hpe P hP D g hg
    (hell.symm ▸ ell.isUnit) hresD hcommD
  let fm := f.map ε.toRingHom
  let gm := g.map ε.toRingHom
  have hf0 : PowerSeries.constantCoeff fm = 0 := by
    simpa only [fm, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, map_zero] using congrArg ε.toRingHom hf
  have hf1 : fm.coeff 1 = 1 := by
    simpa only [fm, PowerSeries.coeff_map, map_one] using congrArg ε.toRingHom hlinear
  have hg0 : PowerSeries.constantCoeff gm = 0 := by
    simpa only [gm, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, map_zero] using congrArg ε.toRingHom hg
  let ellm := Units.map ε.toMonoidHom ell
  have hellm : gm.coeff 1 = (ellm : ZMod p) := by
    change ε (g.coeff 1) = ε (ell : IsLocalRing.ResidueField O)
    exact congrArg ε hell
  have horder_m : orderOf ellm = p - 1 :=
    (order_units_coefficient_map ε.toRingHom ε.injective ell).trans horder
  have hinfinite_m : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero fm hf0
      (hf1 ▸ isUnit_one)) :=
    infinite_order_mapped_coordinate ε.toRingHom ε.injective f hf
      (hlinear ▸ isUnit_one) hinfinite
  have hlimit_m : Tendsto (fun n : ℕ ↦
      (((HahnSeries.ofPowerSeries ℤ (ZMod p) (powerSeriesIterate fm (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1 : ℤ) : PadicInt p)) atTop
      (nhds (FalseTateExtension.kummerRamificationLimit p)) := by
    convert hlimit using 1
    funext n
    rw [order_mapped_iterate_displacement ε.toRingHom ε.injective f hf
      (hlinear ▸ isUnit_one) (p ^ n)]
  have hmapne : mapRingHom ε.toRingHom h ≠ 0 := by
    intro hz
    apply hne
    apply coefficient_map_injective ε.toRingHom ε.injective
    simpa only [map_zero] using hz
  have hmapA : derivative (ZMod p) (mapRingHom ε.toRingHom A) =
      mapRingHom ε.toRingHom h := by
    rw [← mapRingHom_derivative, ← hA]
  exact not_weighted_exact_of_ramification_limit p fm hf0 hf1 hinfinite_m hlimit_m
    gm hg0 ellm hellm horder_m (mapRingHom ε.toRingHom h) (mapRingHom ε.toRingHom A)
    hmapne hmapA
    (coefficient_map_weighted ε.toRingHom f hf (hlinear ▸ isUnit_one) (p - 1) h hwf)
    (coefficient_map_weighted ε.toRingHom g hg (hell.symm ▸ ell.isUnit) (p - 1) h hwg)

end FalseTateNonliftability.CoefficientRing
