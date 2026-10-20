/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Liftability.FieldOfNorms
public import FalseTateExtension.Cyclotomic.InfiniteCharacter
public import FalseTateExtension.FalseTate.StrictAPF
public import FalseTateExtension.FalseTate.TotalRamification
public import FalseTateExtension.FalseTate.Viviani.TauRamification
public import FalseTateExtension.Layers.Galois

/-!
# Ramification numbers of the Kummer iterates

Let `p` be an odd prime, `π` a uniformizer of `ℚ_p`, `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` the false
Tate curve extension, `τ` the generator of `Gal(K_FT/ℚ_p(ζ_{p^∞}))` with Kummer exponent `1`, and
`X = X_{ℚ_p}(K_FT)` the field of norms. For an automorphism `g` of a totally ramified infinite APF
extension `L/K` and a uniformizer `u` of `X_K(L)`, the ramification number of `g` on `X_K(L)` is
`i(g) = v(g(u) - u) - 1 = v_T(f_{g,u} - T) - 1`, where `f_{g,u}` is the coordinate series of `g`
(Yuan, Lemma 2.2 and §3.2).

Proposition 5.1 of Yuan: for every `k ≥ 0` the ramification number of `τ^{p^k}` on `X` is
`d_k = (2 p^{2k+2} + p - 1)/(p + 1)`. It is the ramification number of the restriction of
`τ^{p^k}` to the diagonal layers `L_N = ℚ_p(π^{1/p^N}, ζ_{p^N})` for large `N` (Wintenberger,
Proposition 3.3.2), which is `d_k` for `N ≥ k + 2` (Viviani, Corollary 6.10). Consequently, for
every uniformizer `u` of `X`, `v_T(f_{τ^{p^k},u} - T) = d_k + 1`, `f_{τ,u} = T + O(T²)`, and `τ`
acts on `X` with infinite order. Moreover `d_k → ∞`, and `d_k → (p - 1)/(p + 1)` in `ℤ_p`, a limit
which is not an integer. The identities `d_0 = 2p - 1`, `p ∣ d_k + 1` and `(p + 1) d_k ≤ d_{k+1}`
are `FalseTateExtension.kummerRamificationBreak_zero`,
`FalseTateExtension.kummerRamificationBreak_succ_dvd` and
`FalseTateExtension.kummerRamificationBreak_growth`.

## Main definitions

* `FalseTateNonliftability.kummerRamificationLimit p`: the `p`-adic integer `(p - 1)/(p + 1)`.
* `FalseTateNonliftability.fact_not_finite_falseTateExtension`: `K_FT/ℚ_p` is infinite, as an
  instance.

## Main results

* `FalseTateNonliftability.FieldOfNorms.ramificationNumber_eq_order_coordinateSeries_sub_X`:
  `i(g) = v_T(f_{g,u} - T) - 1`.
* `FalseTateNonliftability.FieldOfNorms.valuation_aut_sub_eq_iff`:
  `v(g(u) - u) = v_T(f_{g,u} - T)`.
* `FalseTateNonliftability.ramificationNumber_kummerGenerator_pow`: `i(τ^{p^k}) = d_k`
  (Yuan, Proposition 5.1 (5.1)).
* `FalseTateNonliftability.order_coordinateSeries_kummerGenerator_pow_sub_X`,
  `FalseTateNonliftability.valuation_aut_kummerGenerator_pow_sub`:
  `v_T(f_{τ^{p^k},u} - T) = v(τ^{p^k}(u) - u) = d_k + 1` for every uniformizer `u`.
* `FalseTateNonliftability.coeff_one_coordinateSeries_kummerGenerator`: `f_{τ,u}'(0) = 1`.
* `FalseTateNonliftability.coordinateSeries_kummerGenerator_pow_ne_X`: `f_{τ^n,u} ≠ T` for
  `n > 0`.
* `FalseTateNonliftability.kummerRamificationBreak_tendsto_atTop`: `d_k → ∞`.
* `FalseTateNonliftability.kummerRamificationBreak_tendsto_padic`: `d_k → (p - 1)/(p + 1)` in
  `ℤ_p` (Yuan, Proposition 5.1 (5.2)).
* `FalseTateNonliftability.kummerRamificationLimit_notMem_range_intCast`: `(p - 1)/(p + 1)` is
  not an integer.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.2, §3.2 and Proposition 5.1.
* J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Proposition 3.3.2.
* M. Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*,
  Corollary 6.10.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger FalseTateExtension PowerSeries WithZero Filter Topology
open scoped ENNReal FalseTateExtension

namespace FalseTateNonliftability

/-- `n - 1 = d` in `EReal` for `n ∈ ℕ∞` if and only if `n = d + 1`. -/
private theorem coe_sub_one_eq_natCast_iff {n : ℕ∞} {d : ℕ} :
    ((n : ℝ≥0∞) : EReal) - 1 = d ↔ n = d + 1 := by
  induction n using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, EReal.coe_ennreal_top]
    rw [← EReal.coe_one, EReal.top_sub_coe]
    simp [eq_comm (a := ⊤)]
  | coe m =>
    rw [ENat.toENNReal_coe, ENNReal.toEReal_natCast, ← EReal.coe_natCast, ← EReal.coe_natCast,
      ← EReal.coe_one, ← EReal.coe_sub, EReal.coe_eq_coe_iff, sub_eq_iff_eq_add]
    norm_cast

namespace FieldOfNorms

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The automorphisms of a totally ramified extension act trivially on the residue field of the
integral closure. -/
private theorem algebraicResidueAut_eq_refl [IsTotallyRamified K L] (g : L ≃ₐ[K] L) :
    algebraicResidueAut K L g = RingEquiv.refl _ := by
  ext a
  obtain ⟨b, rfl⟩ := IsTotallyRamified.algebraMap_surjective (K := K) (L := L) a
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective b
  rw [IsLocalRing.ResidueField.algebraMap_residue, algebraicResidueAut_residue,
    AlgEquiv.commutes]
  rfl

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An integral element `x` of `X_K(L)` with `v(x) = n` in the normalized additive valuation of
the valuation ring has valuation `exp (-n)`. -/
private theorem valuation_coe_of_addVal_eq
    {x : (FieldOfNorms.fieldValuation K L).valuationSubring} {n : ℕ}
    (h : IsDiscreteValuationRing.addVal _ x = n) :
    FieldOfNorms.valuation K L (x : FieldOfNorms K L) = exp (-(n : ℤ)) := by
  have hx : (IsDiscreteValuationRing.maximalIdeal
      (FieldOfNorms.fieldValuation K L).valuationSubring).valuation (FieldOfNorms K L)
      (algebraMap _ (FieldOfNorms K L) x) = exp (-(n : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal, h]
    rfl
  rw [FieldOfNorms.fieldValuation_eq_normalized K L] at hx
  exact hx

variable (u : FieldOfNorms K L) (hu : FieldOfNorms.valuation K L u = exp (-1 : ℤ))

/-- The evaluation `ev_u : κ_L⟦T⟧ ≃ 𝒪_{X_K(L)}` transports the `T`-adic order to the normalized
additive valuation. -/
private theorem addVal_powerSeriesEquiv (A : PowerSeries (integralClosureResidueField K L)) :
    IsDiscreteValuationRing.addVal _ (FieldOfNorms.powerSeriesEquiv K L u hu A) = A.order := by
  by_cases hA : A = 0
  · simp [hA]
  have hne : FieldOfNorms.powerSeriesEquiv K L u hu A ≠ 0 :=
    (map_ne_zero_iff _ (FieldOfNorms.powerSeriesEquiv K L u hu).injective).mpr hA
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hne)
  have hv := FieldOfNorms.powerSeriesEquiv_valuation K L u hu A hA
  rw [valuation_coe_of_addVal_eq K L hm.symm] at hv
  have hm' : m = A.order.toNat := by
    have := exp_injective hv
    omega
  rw [← hm, hm', ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr hA)]

/-- `ev_u(f_{g,u} - T) = g(u) - u`. -/
private theorem coe_powerSeriesEquiv_coordinateSeries_sub_X (g : L ≃ₐ[K] L) :
    (FieldOfNorms.powerSeriesEquiv K L u hu (coordinateSeries K L u hu g - X) :
      FieldOfNorms K L) = FieldOfNorms.aut K L g u - u := by
  rw [← FieldOfNorms.laurentEquiv_powerSeries, map_sub, map_sub, FieldOfNorms.laurentEquiv_X,
    LaurentSeries.coe_algebraMap, laurentEquiv_coordinateSeries]

/-- The ramification number `i(g) = v(g(u) - u) - 1` of an automorphism `g` of a totally ramified
extension `L/K` on `X_K(L)` is `v_T(f_{g,u} - T) - 1` (Yuan, §3.2). -/
theorem ramificationNumber_eq_order_coordinateSeries_sub_X [IsTotallyRamified K L]
    (g : L ≃ₐ[K] L) :
    FieldOfNorms.ramificationNumber K L g =
      (((coordinateSeries K L u hu g - X).order : ℝ≥0∞) : EReal) - 1 := by
  have hres := (FieldOfNorms.residueAut_eq_refl_iff_algebraicResidueAut K L g).mpr
    (algebraicResidueAut_eq_refl K L g)
  let πu : (FieldOfNorms.fieldValuation K L).valuationSubring := ⟨u, hu.le.trans (by simp)⟩
  rw [FieldOfNorms.ramificationNumber_eq_uniformizer K L g hres πu
    (irreducible_of_valuation_exp_neg_one (FieldOfNorms K L) πu hu)]
  have h : FieldOfNorms.integerAut K L g πu - πu =
      FieldOfNorms.powerSeriesEquiv K L u hu (coordinateSeries K L u hu g - X) := by
    apply Subtype.ext
    rw [coe_powerSeriesEquiv_coordinateSeries_sub_X]
    rfl
  rw [h, addVal_powerSeriesEquiv]

/-- `v(g(u) - u) = n` if and only if `v_T(f_{g,u} - T) = n`. -/
theorem valuation_aut_sub_eq_iff (g : L ≃ₐ[K] L) (n : ℕ) :
    FieldOfNorms.valuation K L (FieldOfNorms.aut K L g u - u) = exp (-(n : ℤ)) ↔
      (coordinateSeries K L u hu g - X).order = (n : ℕ∞) := by
  rw [← coe_powerSeriesEquiv_coordinateSeries_sub_X K L u hu]
  by_cases hA : coordinateSeries K L u hu g - X = 0
  · simp only [hA, map_zero, ZeroMemClass.coe_zero, PowerSeries.order_zero, ENat.top_ne_natCast,
      iff_false]
    exact fun h ↦ exp_ne_zero h.symm
  have htop := PowerSeries.order_eq_top.not.mpr hA
  rw [FieldOfNorms.powerSeriesEquiv_valuation K L u hu _ hA, exp_injective.eq_iff, neg_inj,
    Nat.cast_inj]
  constructor
  · intro h
    rw [← h, ENat.natCast_toNat htop]
  · intro h
    rw [h, ENat.toNat_natCast]

end FieldOfNorms

section FalseTate

variable (p : ℕ) [Fact p.Prime]

/-- `ℚ_p(π^{1/p^∞}, ζ_{p^∞})/ℚ_p` is an infinite extension. -/
instance fact_not_finite_falseTateExtension (π : ℚ_[p]) :
    Fact (¬ Module.Finite ℚ_[p] (falseTateExtension p π)) :=
  ⟨not_finiteDimensional_falseTateExtension_padic p π⟩

variable [Fact (p ≠ 2)] (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]

/-- The ramification number of `τ^{p^k}` on the diagonal layer `L_N ⊆ K_FT` is `d_k` for
`N ≥ k + 2`. -/
private theorem ramificationNumber_falseTateDiagonalSubfield (k N : ℕ) (hN : k + 2 ≤ N) :
    FiniteIntermediateField.ramificationNumber ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
      ((τ p π).val ^ p ^ k) (falseTateDiagonalSubfield p (π : ℚ_[p]) N) =
      kummerRamificationBreak p k := by
  let e := falseTateDiagonalSubfieldEquiv p (π : ℚ_[p]) N
  let t := tauPowRestrict p π N k
  let s := e.symm.trans (t.trans e)
  have hs (a : (falseTateDiagonalSubfield p (π : ℚ_[p]) N).val) :
      (s a : falseTateExtension p (π : ℚ_[p])) = ((τ p π).val ^ p ^ k) a := by
    obtain ⟨x, rfl⟩ := e.surjective a
    simp only [s, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    exact infiniteLayerRestriction_commutes p (π : ℚ_[p]) N _ x
  have h₁ : s.toAlgHom.comp e.toAlgHom = e.toAlgHom.comp t.toAlgHom := by
    ext x
    simp [s]
  have h₂ : (AlgHom.id ℚ_[p] _).comp e.toAlgHom = e.toAlgHom.comp (AlgHom.id ℚ_[p] _) := rfl
  rw [FiniteIntermediateField.ramificationNumber_eq_aut _ _ _ _ s hs,
    ← embeddingRamificationNumber_aut, ← embeddingNumber_precomp_algEquiv ℚ_[p] e, h₁, h₂,
    embeddingRamificationNumber_comp, embeddingRamificationNumber_aut,
    ramificationOrder_tauPowRestrict p π N k hN]
  exact coe_sub_one_eq_natCast_iff.mpr rfl

/-- The ramification number of `τ^{p^k}` on the field of norms `X_{ℚ_p}(K_FT)` is
`d_k = (2 p^{2k+2} + p - 1)/(p + 1)` (Yuan, Proposition 5.1 (5.1)). -/
theorem ramificationNumber_kummerGenerator_pow (k : ℕ) :
    FieldOfNorms.ramificationNumber ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
      ((τ p π).val ^ p ^ k) = kummerRamificationBreak p k := by
  obtain ⟨E, hE⟩ := exists_finiteIntermediateField_ramificationNumber_eq ℚ_[p]
    (falseTateExtension p (π : ℚ_[p])) ((τ p π).val ^ p ^ k)
  obtain ⟨n, hn⟩ := exists_le_falseTateDiagonalSubfield p (π : ℚ_[p]) E
  rw [← hE _ (hn.trans (falseTateDiagonalSubfield_mono p _ (le_max_left n (k + 2)))),
    ramificationNumber_falseTateDiagonalSubfield p π k _ (le_max_right n (k + 2))]

variable {p π} (u : FontaineWintenberger.FieldOfNorms ℚ_[p] (falseTateExtension p (π : ℚ_[p])))
  (hu : FontaineWintenberger.FieldOfNorms.valuation ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u =
    exp (-1 : ℤ))

/-- `v_T(f_{τ^{p^k},u} - T) = d_k + 1` for every uniformizer `u` of `X_{ℚ_p}(K_FT)`
(Yuan, Proposition 5.1). -/
theorem order_coordinateSeries_kummerGenerator_pow_sub_X (k : ℕ) :
    (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      ((τ p π).val ^ p ^ k) - X).order = ((kummerRamificationBreak p k + 1 : ℕ) : ℕ∞) := by
  have h := FieldOfNorms.ramificationNumber_eq_order_coordinateSeries_sub_X _ _ u hu
    ((τ p π).val ^ p ^ k)
  rw [ramificationNumber_kummerGenerator_pow] at h
  exact_mod_cast coe_sub_one_eq_natCast_iff.mp h.symm

include hu in
/-- `v(τ^{p^k}(u) - u) = d_k + 1` for every uniformizer `u` of `X_{ℚ_p}(K_FT)`
(Yuan, Proposition 5.1). -/
theorem valuation_aut_kummerGenerator_pow_sub (k : ℕ) :
    FontaineWintenberger.FieldOfNorms.valuation ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
      (FontaineWintenberger.FieldOfNorms.aut ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
        ((τ p π).val ^ p ^ k) u - u) = exp (-((kummerRamificationBreak p k + 1 : ℕ) : ℤ)) :=
  (FieldOfNorms.valuation_aut_sub_eq_iff _ _ u hu _ _).mpr
    (order_coordinateSeries_kummerGenerator_pow_sub_X u hu k)

/-- `f_{τ,u} = T + O(T²)` for every uniformizer `u` of `X_{ℚ_p}(K_FT)`. -/
theorem coeff_one_coordinateSeries_kummerGenerator :
    (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      (τ p π).val).coeff 1 = 1 := by
  have h := order_coordinateSeries_kummerGenerator_pow_sub_X u hu 0
  rw [pow_zero, pow_one, kummerRamificationBreak_zero p (Fact.out : p.Prime).one_le] at h
  have hlt : ((1 : ℕ) : ℕ∞) < (FieldOfNorms.coordinateSeries ℚ_[p]
      (falseTateExtension p (π : ℚ_[p])) u hu (τ p π).val - X).order := by
    have hp := (Fact.out : p.Prime).two_le
    rw [h]
    exact_mod_cast (by omega : 1 < 2 * p - 1 + 1)
  simpa [sub_eq_zero] using PowerSeries.coeff_of_lt_order 1 hlt

/-- `τ` acts on `X_{ℚ_p}(K_FT)` with infinite order: `f_{τ^n,u} ≠ T` for `n > 0`
(Yuan, Proposition 5.1). -/
theorem coordinateSeries_kummerGenerator_pow_ne_X {n : ℕ} (hn : 0 < n) :
    FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      ((τ p π).val ^ n) ≠ X := by
  intro h
  have hr := FieldOfNorms.ramificationNumber_eq_order_coordinateSeries_sub_X _ _ u hu
    ((τ p π).val ^ n)
  rw [h, sub_self, PowerSeries.order_zero, ENat.toENNReal_top, EReal.coe_ennreal_top,
    ← EReal.coe_one, EReal.top_sub_coe,
    FontaineWintenberger.FieldOfNorms.ramificationNumber_eq_top_iff] at hr
  have hn' := padicKummerExponent_kummerGenerator_pow p π n
  have h0 := padicKummerExponent_kummerGenerator_pow p π 0
  rw [hr] at hn'
  rw [pow_zero, hn'] at h0
  exact hn.ne' (by exact_mod_cast h0)

end FalseTate

section PadicLimit

variable (p : ℕ) [Fact p.Prime]

/-- `d_k → ∞` (Yuan, Proposition 5.1 (2)). -/
theorem kummerRamificationBreak_tendsto_atTop :
    Tendsto (kummerRamificationBreak p) atTop atTop :=
  (kummerRamificationBreak_strictMono p (Fact.out : p.Prime).two_le).tendsto_atTop

/-- `|p|_p < 1`. -/
private theorem norm_natCast_lt_one : ‖(p : ℤ_[p])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- `p + 1` is a unit of `ℤ_p`. -/
private theorem isUnit_natCast_add_one : IsUnit ((p : ℤ_[p]) + 1) := by
  have hp := norm_natCast_lt_one p
  rw [PadicInt.isUnit_iff, PadicInt.norm_add_eq_max_of_ne (by simpa using hp.ne), norm_one,
    max_eq_right hp.le]

/-- The `p`-adic integer `(p - 1)/(p + 1)`. -/
def kummerRamificationLimit : ℤ_[p] :=
  ((p : ℤ_[p]) - 1) * Ring.inverse ((p : ℤ_[p]) + 1)

/-- `(p - 1)/(p + 1) · (p + 1) = p - 1`. -/
theorem kummerRamificationLimit_mul_add_one :
    kummerRamificationLimit p * ((p : ℤ_[p]) + 1) = p - 1 := by
  rw [kummerRamificationLimit, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_natCast_add_one p),
    mul_one]

/-- `d_k - (p - 1)/(p + 1) = 2 p^{2k+2}/(p + 1)`. -/
private theorem kummerRamificationBreak_sub_kummerRamificationLimit (k : ℕ) :
    (kummerRamificationBreak p k : ℤ_[p]) - kummerRamificationLimit p =
      2 * (p : ℤ_[p]) ^ (2 * k + 2) * Ring.inverse ((p : ℤ_[p]) + 1) := by
  have h := congrArg ((↑) : ℕ → ℤ_[p])
    (kummerRamificationBreak_mul p k (Fact.out : p.Prime).one_le)
  push_cast [Nat.cast_sub (Fact.out : p.Prime).one_le] at h
  have hu := Ring.mul_inverse_cancel _ (isUnit_natCast_add_one p)
  rw [kummerRamificationLimit]
  linear_combination h * Ring.inverse ((p : ℤ_[p]) + 1) -
    (kummerRamificationBreak p k : ℤ_[p]) * hu

/-- `d_k → (p - 1)/(p + 1)` in `ℤ_p` (Yuan, Proposition 5.1 (5.2)). -/
theorem kummerRamificationBreak_tendsto_padic :
    Tendsto (fun k ↦ (kummerRamificationBreak p k : ℤ_[p])) atTop
      (𝓝 (kummerRamificationLimit p)) := by
  have he : Tendsto (fun k : ℕ ↦ 2 * k + 2) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (by omega : k ≤ 2 * k + 2)) tendsto_id
  have hz := (((tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_natCast_lt_one p)).comp
    he).const_mul 2).mul_const (Ring.inverse ((p : ℤ_[p]) + 1))
  rw [mul_zero, zero_mul] at hz
  refine tendsto_sub_nhds_zero_iff.mp (hz.congr fun k ↦ ?_)
  rw [kummerRamificationBreak_sub_kummerRamificationLimit, Function.comp_apply]

/-- `(p - 1)/(p + 1) ∈ ℤ_p` is not an integer (Yuan, Proposition 5.1 (5.2)). -/
theorem kummerRamificationLimit_notMem_range_intCast :
    kummerRamificationLimit p ∉ Set.range ((↑) : ℤ → ℤ_[p]) := by
  rintro ⟨z, hz⟩
  have h := kummerRamificationLimit_mul_add_one p
  rw [← hz] at h
  have hz' : z * ((p : ℤ) + 1) = (p : ℤ) - 1 := by exact_mod_cast h
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hz₀ : 0 < z := by nlinarith
  nlinarith

end PadicLimit

end FalseTateNonliftability
