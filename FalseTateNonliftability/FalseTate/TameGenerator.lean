/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.FalseTate.RamificationNumbers
public import FalseTateExtension.FalseTate.TranslationKernel
public import FontaineWintenberger.FieldOfNorms.Galois.Action
public import FontaineWintenberger.Ramification.Lower.Teichmuller

/-!
# The tame generator and its linear coefficient

Let `p` be an odd prime, `π` a uniformizer of `ℚ_p`, `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})`,
`K_Kum = ℚ_p(π^{1/p^∞})`, `χ : Gal(K_FT/ℚ_p) → ℤ_pˣ` the `p`-adic cyclotomic character and `τ` the
generator of `Gal(K_FT/ℚ_p(ζ_{p^∞})) ≅ ℤ_p` with Kummer exponent `1`. The character `χ` restricts
to an isomorphism `Gal(K_FT/K_Kum) ≅ ℤ_pˣ ≅ μ_{p-1} × (1 + p ℤ_p)`. The tame generator `δ` is the
element of `Gal(K_FT/K_Kum)` whose character `χ(δ) = ω(g)` is the Teichmüller representative of a
fixed generator `g` of `𝔽_pˣ`; it generates the torsion subgroup of `Gal(K_FT/K_Kum)`, and
`δ τ δ⁻¹ = τ^{χ(δ)}` (Yuan, Lemma 1.2 (3)).

Yuan, Lemma 5.3: for every uniformizer `u` of the field of norms `X_{ℚ_p}(K_FT)`, whose residue
field `κ_L` is `𝔽_p` as `K_FT/ℚ_p` is totally ramified, the coordinate series of `δ` is
`f_{δ,u} = χ(δ) T + O(T²)`. Hence its linear coefficient has multiplicative order `p - 1`. This
follows from `f_{τ,u} = T + α T^{2p} + O(T^{2p+1})` with `α ≠ 0` (`d_0 = 2p - 1`, Yuan,
Proposition 5.1) by comparing the coefficients of `T^{2p}` in
`f_{τ,u} ∘ f_{δ,u} = f_{δ,u} ∘ f_{τ^{χ(δ)},u}`.

## Main definitions

* `FalseTateNonliftability.tameUnit p`: the Teichmüller representative `ω(g) ∈ ℤ_pˣ` of a fixed
  generator `g` of `𝔽_pˣ`.
* `FalseTateNonliftability.tameGenerator p π`, with scoped notation `δ`: the tame generator
  `δ ∈ Gal(K_FT/K_Kum)` with `χ(δ) = ω(g)`.

## Main results

* `FalseTateNonliftability.padicCyclotomicCharacter_tameGenerator`: `χ(δ) = ω(g)`.
* `FalseTateNonliftability.orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator`:
  `χ(δ) mod p` has order `p - 1` in `𝔽_pˣ`.
* `FalseTateNonliftability.falseTateKummerFixing_mul_kummerGenerator`,
  `FalseTateNonliftability.tameGenerator_mul_kummerGenerator`: `σ τ = τ^{χ(σ)} σ` for
  `σ ∈ Gal(K_FT/K_Kum)`, in particular `δ τ = τ^{χ(δ)} δ` (Yuan, Lemma 1.2 (3)).
* `FalseTateNonliftability.coeff_one_coordinateSeries_falseTateKummerFixing`,
  `FalseTateNonliftability.coeff_one_coordinateSeries_tameGenerator`: `f_{σ,u}'(0)` is the image
  of `χ(σ) mod p` in `κ_L`, for `σ ∈ Gal(K_FT/K_Kum)` and for `σ = δ` (Yuan, Lemma 5.3).
* `FalseTateNonliftability.orderOf_coeff_one_coordinateSeries_falseTateKummerFixing`,
  `FalseTateNonliftability.orderOf_coeff_one_coordinateSeries_tameGenerator`: `f_{σ,u}'(0)` has
  multiplicative order `p - 1` if `χ(σ) mod p` has order `p - 1`, in particular for `σ = δ`
  (Yuan, Lemma 5.3).

## Implementation notes

Yuan, Lemma 1.2 (3) lets `δ` be any generator of the torsion subgroup of `Gal(K_FT/K_Kum)`. Here
`δ` is the element with `χ(δ) = ω(g)` for a generator `g` of `𝔽_pˣ` chosen once and for all. The
proofs use only that `χ(δ) mod p` generates `𝔽_pˣ`, and Lemma 5.3 is also stated for every
`σ ∈ Gal(K_FT/K_Kum)` with this property, which includes every generator of the torsion
subgroup.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 1.2, Proposition 5.1 and Lemma 5.3.
* T. Liu, *On lattices in semi-stable representations: a proof of a conjecture of Breuil*,
  Compos. Math. 144 (2008), 61–88, Lemma 5.1.2.
* F. Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, J. Théor.
  Nombres Bordeaux 16 (2004), 779–816, Corollary 6.2.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger FalseTateExtension PowerSeries WithZero Filter Topology
open scoped FalseTateExtension

namespace FalseTateNonliftability

section Jets

/-- Let `f_τ ≡ T + α T^{2q} mod T^{2q+1}` with `α ≠ 0`, `f_σ ≡ T + r α T^{2q} mod T^{2q+1}` and
`f_δ = λ T + O(T²)` with `λ ≠ 0` and `λ^q = λ`. If `f_τ ∘ f_δ = f_δ ∘ f_σ`, then `λ = r`. -/
private theorem coeff_one_eq_of_subst_eq {κ : Type*} [Field κ] {fτ fδ fσ : κ⟦X⟧} {q : ℕ}
    (hq : 1 ≤ q) (hδ : fδ.constantCoeff = 0) (hσ : fσ.constantCoeff = 0)
    (hτ : X ^ (2 * q) ∣ fτ - X) (hα : coeff (2 * q) (fτ - X) ≠ 0) {r : κ}
    (hσr : ∀ j ≤ 2 * q, coeff j (fσ - X) = r * coeff j (fτ - X)) (hδ₁ : fδ.coeff 1 ≠ 0)
    (hδq : fδ.coeff 1 ^ q = fδ.coeff 1) (hrel : fτ.subst fδ = fδ.subst fσ) :
    fδ.coeff 1 = r := by
  have hσX : X ^ (2 * q) ∣ fσ - X := X_pow_dvd_iff.mpr fun j hj ↦ by
    rw [hσr j hj.le, X_pow_dvd_iff.mp hτ j hj, mul_zero]
  have h := coeff_subst_sub_coeff_of_dvd_outer hδ hτ
  rw [hrel, coeff_subst_sub_coeff_of_dvd_inner hσ hσX fδ (by omega) le_rfl, hσr _ le_rfl,
    pow_mul', hδq] at h
  -- `h : λ (r α) = α λ²`
  exact mul_left_cancel₀ (mul_ne_zero hα hδ₁) (by linear_combination -h)

end Jets

section Teichmuller

variable (p : ℕ) [Fact p.Prime]

/-- Reduction modulo `p` of an element of `𝒪[ℚ_p] = ℤ_p` is its residue class in
`𝓀[ℚ_p] = 𝔽_p`. -/
private theorem toZMod_padicValuationSubringEquiv (x : 𝒪[ℚ_[p]]) :
    PadicInt.toZMod (padicValuationSubringEquiv p x) =
      padicResidueFieldEquiv p (IsLocalRing.residue _ x) :=
  rfl

/-- The Teichmüller representative `ω(g) ∈ ℤ_pˣ` of a fixed generator `g` of `𝔽_pˣ`: the
`(p - 1)`-th root of unity in `ℤ_p` with `ω(g) ≡ g mod p`. It generates the torsion subgroup
`μ_{p-1}` of `ℤ_pˣ`. -/
def tameUnit : ℤ_[p]ˣ :=
  Units.map (((padicValuationSubringEquiv p).toMonoidHom.comp
      (residueTeichmuller 𝒪[ℚ_[p]] p).toMonoidHom).comp
        (padicResidueFieldEquiv p).symm.toMonoidHom)
    (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)).choose

/-- `ω(g) mod p` has order `p - 1` in `𝔽_pˣ`. -/
theorem orderOf_map_toZMod_tameUnit :
    orderOf (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom (tameUnit p)) =
      p - 1 := by
  have h : Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom (tameUnit p) =
      (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)).choose := by
    ext
    simp [tameUnit, toZMod_padicValuationSubringEquiv]
  rw [h, (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)).choose_spec,
    Nat.card_eq_fintype_card, ZMod.card_units]

end Teichmuller

section TameGenerator

variable (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)] (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]

/-- The tame generator `δ ∈ Gal(K_FT/K_Kum)`: the automorphism whose cyclotomic character
`χ(δ) = ω(g)` is the Teichmüller representative of a fixed generator `g` of `𝔽_pˣ`. As
`χ : Gal(K_FT/K_Kum) ≅ ℤ_pˣ`, it generates the torsion subgroup of `Gal(K_FT/K_Kum)`
(Yuan, Lemma 1.2 (3)). -/
def tameGenerator : falseTateKummerFixing p (π : ℚ_[p]) :=
  (kummerFixingEquivCyclotomicImage p π).symm
    ⟨tameUnit p, cyclotomicExtensionCharacter_surjective_padic p (tameUnit p)⟩

@[inherit_doc] scoped notation "δ" => tameGenerator

/-- `χ(δ) = ω(g)`. -/
@[simp]
theorem padicCyclotomicCharacter_tameGenerator :
    padicCyclotomicCharacter p (π : ℚ_[p]) (δ p π).val = tameUnit p :=
  congrArg Subtype.val ((kummerFixingEquivCyclotomicImage p π).apply_symm_apply _)

/-- `χ(δ) mod p` has order `p - 1` in `𝔽_pˣ`. -/
theorem orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator :
    orderOf (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom
      (padicCyclotomicCharacter p (π : ℚ_[p]) (δ p π).val)) = p - 1 := by
  rw [padicCyclotomicCharacter_tameGenerator, orderOf_map_toZMod_tameUnit]

/-- `b(τ^N) = N`: the element of `ker χ` with Kummer exponent `N` is `τ^N`. -/
private theorem kummerKernelEquivPadicInt_symm_natCast (N : ℕ) :
    ((kummerKernelEquivPadicInt p π).symm (N : ℤ_[p])).toMul = τ p π ^ N := by
  rw [← nsmul_one, map_nsmul, toMul_nsmul]
  rfl

/-- `σ τ = τ^{χ(σ)} σ` for every `σ ∈ Gal(K_FT/K_Kum)`, where `τ^a` for `a ∈ ℤ_p` is the element
of `Gal(K_FT/ℚ_p(ζ_{p^∞}))` with Kummer exponent `a` (Yuan, Lemma 1.2 (3)). -/
theorem falseTateKummerFixing_mul_kummerGenerator (σ : falseTateKummerFixing p (π : ℚ_[p])) :
    σ.val * (τ p π).val = ((kummerKernelEquivPadicInt p π).symm
      (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val : ℤ_[p])).toMul.val * σ.val := by
  have hb := (mem_falseTateKummerFixing_iff p (π : ℚ_[p]) _).mp σ.property
  set t := ((kummerKernelEquivPadicInt p π).symm
    (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val : ℤ_[p])).toMul
  have ht : padicKummerExponent p (π : ℚ_[p]) t.val =
      padicCyclotomicCharacter p (π : ℚ_[p]) σ.val :=
    (kummerKernelEquivPadicInt p π).apply_symm_apply _
  apply padicCoordinates_injective p (π : ℚ_[p])
  refine Prod.ext ?_ ?_
  · change padicKummerExponent p (π : ℚ_[p]) _ = padicKummerExponent p (π : ℚ_[p]) _
    rw [padicKummerExponent_mul, padicKummerExponent_mul, hb, ht, t.property,
      padicKummerExponent_kummerGenerator]
    simp
  · change padicCyclotomicCharacter p (π : ℚ_[p]) _ = padicCyclotomicCharacter p (π : ℚ_[p]) _
    rw [map_mul, map_mul, (τ p π).property, t.property, mul_one, one_mul]

/-- `δ τ = τ^{χ(δ)} δ`, where `τ^a` for `a ∈ ℤ_p` is the element of `Gal(K_FT/ℚ_p(ζ_{p^∞}))` with
Kummer exponent `a` (Yuan, Lemma 1.2 (3)). -/
theorem tameGenerator_mul_kummerGenerator :
    (δ p π).val * (τ p π).val = ((kummerKernelEquivPadicInt p π).symm
      (padicCyclotomicCharacter p (π : ℚ_[p]) (δ p π).val : ℤ_[p])).toMul.val * (δ p π).val :=
  falseTateKummerFixing_mul_kummerGenerator p π (δ p π)

end TameGenerator

namespace FieldOfNorms

variable {K : Type*} [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
  {L : Type*} [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (u : FontaineWintenberger.FieldOfNorms K L)
  (hu : FontaineWintenberger.FieldOfNorms.valuation K L u = exp (-1 : ℤ))

/-- If `g(u) ≡ h(u)` modulo the `m`-th power of the maximal ideal of `X_K(L)`, then `f_{g,u}` and
`f_{h,u}` agree below degree `m`. -/
private theorem coeff_coordinateSeries_eq_of_valuation_le (g h : L ≃ₐ[K] L) {m : ℕ}
    (hgh : FontaineWintenberger.FieldOfNorms.valuation K L
      (FontaineWintenberger.FieldOfNorms.aut K L g u -
        FontaineWintenberger.FieldOfNorms.aut K L h u) ≤ exp (-(m : ℤ)))
    {j : ℕ} (hj : j < m) :
    (coordinateSeries K L u hu g).coeff j = (coordinateSeries K L u hu h).coeff j := by
  rw [← laurentEquiv_coordinateSeries K L u hu, ← laurentEquiv_coordinateSeries K L u hu,
    ← map_sub, FontaineWintenberger.FieldOfNorms.laurentEquiv_valuation, ← map_sub] at hgh
  have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero _).mp hgh j (by omega)
  rwa [HahnSeries.ofPowerSeries_apply_coeff, map_sub, sub_eq_zero] at h

end FieldOfNorms

section LinearCoefficient

variable {p : ℕ} [Fact p.Prime] [Fact (p ≠ 2)] {π : 𝒪[ℚ_[p]]} [Fact (Irreducible π)]
  (u : FontaineWintenberger.FieldOfNorms ℚ_[p] (falseTateExtension p (π : ℚ_[p])))
  (hu : FontaineWintenberger.FieldOfNorms.valuation ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u =
    exp (-1 : ℤ))

include hu in
/-- For `a ∈ ℤ_p` and `m ∈ ℕ` there is `N ∈ ℕ` with `N ≡ a mod p` and
`v(τ^N(u) - τ^a(u)) ≥ m + 2`, where `τ^a ∈ ker χ` is the element with Kummer exponent `a`. -/
private theorem exists_natCast_valuation_aut_sub_le (a : ℤ_[p]) (m : ℕ) :
    ∃ N : ℕ, PadicInt.toZMod (N : ℤ_[p]) = PadicInt.toZMod a ∧
      FontaineWintenberger.FieldOfNorms.valuation ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
        (FontaineWintenberger.FieldOfNorms.aut ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
            ((τ p π).val ^ N) u -
          FontaineWintenberger.FieldOfNorms.aut ℚ_[p] (falseTateExtension p (π : ℚ_[p]))
            ((kummerKernelEquivPadicInt p π).symm a).toMul.val u) ≤
        exp (-((m + 2 : ℕ) : ℤ)) := by
  set φ := fun b : ℤ_[p] ↦ FontaineWintenberger.FieldOfNorms.aut ℚ_[p]
    (falseTateExtension p (π : ℚ_[p])) ((kummerKernelEquivPadicInt p π).symm b).toMul.val u
  have hφ : Continuous fun b ↦ φ b - φ a :=
    ((FontaineWintenberger.FieldOfNorms.continuous_aut_apply _ _ u).comp
      (continuous_subtype_val.comp
        (continuous_toMul.comp (kummerKernelEquivPadicInt p π).symm.continuous))).sub
      continuous_const
  have h₀ : {x | Valued.v x ≤ exp (-((m + 2 : ℕ) : ℤ))} ∈
      𝓝 (φ a - φ a) := by
    rw [sub_self]
    exact (Valued.nhds_zero_hasBasis_integer_closedBall _ u hu).mem_of_mem trivial
  obtain ⟨_, ⟨N, rfl⟩, hN, hN'⟩ := PadicInt.denseRange_natCast.inter_nhds_nonempty
    (inter_mem (hφ.continuousAt.preimage_mem_nhds h₀) (Metric.ball_mem_nhds a one_pos))
  refine ⟨N, ?_, ?_⟩
  · have h : (N : ℤ_[p]) - a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, ← dist_eq_norm]
      exact hN'
    rwa [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero] at h
  · have h : φ N = FontaineWintenberger.FieldOfNorms.aut ℚ_[p]
        (falseTateExtension p (π : ℚ_[p])) ((τ p π).val ^ N) u := by
      simp only [φ, kummerKernelEquivPadicInt_symm_natCast, SubgroupClass.coe_pow]
    rw [← h]
    exact hN

/-- `f_{τ,u} ≡ T + α T^{2p} mod T^{2p+1}` with `α ≠ 0`, as `v_T(f_{τ,u} - T) = d_0 + 1 = 2p`. -/
private theorem coeff_coordinateSeries_kummerGenerator_sub_X :
    coeff (2 * p) (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
        (τ p π).val - X) ≠ 0 ∧
      X ^ (2 * p) ∣ FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
        (τ p π).val - X := by
  have h := order_coordinateSeries_kummerGenerator_pow_sub_X u hu 0
  rw [pow_zero, pow_one, kummerRamificationBreak_zero p (Fact.out : p.Prime).one_le,
    Nat.sub_add_cancel (by have := (Fact.out : p.Prime).two_le; omega)] at h
  exact ⟨(order_eq_nat.mp h).1, X_pow_dvd_iff.mpr (order_eq_nat.mp h).2⟩

/-- For `a ∈ ℤ_p` there is `N ∈ ℕ` with `N ≡ a mod p` and
`f_{τ^a,u} ≡ f_{τ,u}^{∘N} ≡ T + N α T^{2p} mod T^{2p+1}`, where `f_{τ,u} ≡ T + α T^{2p}`. -/
private theorem exists_natCast_coeff_coordinateSeries_sub_X_eq (a : ℤ_[p]) :
    ∃ N : ℕ, PadicInt.toZMod (N : ℤ_[p]) = PadicInt.toZMod a ∧ ∀ j ≤ 2 * p,
      coeff j (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
        ((kummerKernelEquivPadicInt p π).symm a).toMul.val - X) =
      (N : integralClosureResidueField ℚ_[p] (falseTateExtension p (π : ℚ_[p]))) *
        coeff j (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
          (τ p π).val - X) := by
  obtain ⟨N, hN, hv⟩ := exists_natCast_valuation_aut_sub_le u hu a (2 * p)
  refine ⟨N, hN, fun j hj ↦ ?_⟩
  have hp := (Fact.out : p.Prime).two_le
  have hpow :=
    (FieldOfNorms.coordinateFamily ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu).series_pow
      (τ p π).val N
  simp only [FieldOfNorms.coordinateFamily_series] at hpow
  rw [map_sub, ← FieldOfNorms.coeff_coordinateSeries_eq_of_valuation_le u hu _ _ hv
    (show j < 2 * p + 2 by omega), ← map_sub, hpow]
  exact coeff_iterate_sub_X (FieldOfNorms.constantCoeff_coordinateSeries _ _ u hu _) (by omega)
    (coeff_coordinateSeries_kummerGenerator_sub_X u hu).2 N hj

omit [Fact (p ≠ 2)] [Fact (Irreducible π)] in
/-- If `N ≡ a mod p`, then `N` is the image of `a mod p` in `κ_L`. -/
private theorem natCast_eq_algebraMap_toZMod {N : ℕ} {a : ℤ_[p]}
    (h : PadicInt.toZMod (N : ℤ_[p]) = PadicInt.toZMod a) :
    (N : integralClosureResidueField ℚ_[p] (falseTateExtension p (π : ℚ_[p]))) =
      algebraMap 𝓀[ℚ_[p]] _ ((padicResidueFieldEquiv p).symm (PadicInt.toZMod a)) := by
  rw [← h, map_natCast, map_natCast, map_natCast]

/-- Let `σ ∈ Gal(K_FT/K_Kum)`. The linear coefficient of `f_{σ,u}` is the image of `χ(σ) mod p` in
`κ_L = 𝔽_p`: for every uniformizer `u` of `X_{ℚ_p}(K_FT)`, `f_{σ,u} = χ(σ) T + O(T²)` (Yuan,
Lemma 5.3, for every element of `Gal(K_FT/K_Kum)`). -/
theorem coeff_one_coordinateSeries_falseTateKummerFixing
    (σ : falseTateKummerFixing p (π : ℚ_[p])) :
    (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu σ.val).coeff 1 =
      algebraMap 𝓀[ℚ_[p]] (integralClosureResidueField ℚ_[p] (falseTateExtension p (π : ℚ_[p])))
        ((padicResidueFieldEquiv p).symm
          (PadicInt.toZMod (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val : ℤ_[p]))) := by
  obtain ⟨N, hN, hσ⟩ := exists_natCast_coeff_coordinateSeries_sub_X_eq u hu
    (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val : ℤ_[p])
  obtain ⟨hα, hτ⟩ := coeff_coordinateSeries_kummerGenerator_sub_X u hu
  obtain ⟨μ, hμ⟩ := IsTotallyRamified.algebraMap_surjective (K := ℚ_[p])
    (L := falseTateExtension p (π : ℚ_[p]))
    ((FieldOfNorms.coordinateSeries ℚ_[p] _ u hu σ.val).coeff 1)
  have hμp : μ ^ p = μ := (padicResidueFieldEquiv p).injective (by rw [map_pow, ZMod.pow_card])
  have hrel := congrArg (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u
    hu) (falseTateKummerFixing_mul_kummerGenerator p π σ)
  rw [FieldOfNorms.coordinateSeries_mul, FieldOfNorms.coordinateSeries_mul] at hrel
  rw [← natCast_eq_algebraMap_toZMod hN]
  exact coeff_one_eq_of_subst_eq (Fact.out : p.Prime).one_le
    (FieldOfNorms.constantCoeff_coordinateSeries _ _ u hu _)
    (FieldOfNorms.constantCoeff_coordinateSeries _ _ u hu _) hτ hα hσ
    (FieldOfNorms.isUnit_coeff_one_coordinateSeries _ _ u hu _).ne_zero
    (by rw [← hμ, ← map_pow, hμp]) hrel

/-- The linear coefficient of `f_{δ,u}` is the image of `χ(δ) mod p` in `κ_L = 𝔽_p`: for every
uniformizer `u` of `X_{ℚ_p}(K_FT)`, `f_{δ,u} = χ(δ) T + O(T²)` (Yuan, Lemma 5.3). -/
theorem coeff_one_coordinateSeries_tameGenerator :
    (FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      (δ p π).val).coeff 1 =
      algebraMap 𝓀[ℚ_[p]] (integralClosureResidueField ℚ_[p] (falseTateExtension p (π : ℚ_[p])))
        ((padicResidueFieldEquiv p).symm
          (PadicInt.toZMod (padicCyclotomicCharacter p (π : ℚ_[p]) (δ p π).val : ℤ_[p]))) :=
  coeff_one_coordinateSeries_falseTateKummerFixing u hu (δ p π)

/-- Let `σ ∈ Gal(K_FT/K_Kum)` be such that `χ(σ) mod p` has order `p - 1` in `𝔽_pˣ`, for instance
a generator of the torsion subgroup of `Gal(K_FT/K_Kum)`. Then the linear coefficient of `f_{σ,u}`
has multiplicative order `p - 1` (Yuan, Lemma 5.3). -/
theorem orderOf_coeff_one_coordinateSeries_falseTateKummerFixing
    {σ : falseTateKummerFixing p (π : ℚ_[p])}
    (hσ : orderOf (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom
      (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val)) = p - 1) :
    orderOf ((FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      σ.val).coeff 1) = p - 1 := by
  rw [coeff_one_coordinateSeries_falseTateKummerFixing, ← hσ, ← orderOf_units]
  -- `𝔽_p → 𝓀[ℚ_p] → κ_L` is injective
  exact orderOf_injective
    ((algebraMap 𝓀[ℚ_[p]] _).comp (padicResidueFieldEquiv p).symm.toRingHom).toMonoidHom
    (RingHom.injective _) _

/-- The linear coefficient of `f_{δ,u}` has multiplicative order `p - 1` (Yuan, Lemma 5.3). -/
theorem orderOf_coeff_one_coordinateSeries_tameGenerator :
    orderOf ((FieldOfNorms.coordinateSeries ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u hu
      (δ p π).val).coeff 1) = p - 1 :=
  orderOf_coeff_one_coordinateSeries_falseTateKummerFixing u hu
    (orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator p π)

end LinearCoefficient

end FalseTateNonliftability
