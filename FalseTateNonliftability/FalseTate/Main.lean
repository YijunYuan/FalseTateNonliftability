/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Obstruction
public import FalseTateNonliftability.FalseTate.RamificationNumbers
public import FalseTateNonliftability.FalseTate.TameGenerator
public import FalseTateNonliftability.Liftability.IsLiftable

/-!
# Non-liftability of the field of norms of the false Tate curve extension

Let `p` be an odd prime, `π` a uniformizer of `ℚ_p`, `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` the false
Tate curve extension and `X = X_{ℚ_p}(K_FT)` its field of norms, with residue field `𝔽_p`. Let
`τ` be the generator of `Gal(K_FT/ℚ_p(ζ_{p^∞}))` with Kummer exponent `1` and `δ` the tame
generator of `Gal(K_FT/ℚ_p(π^{1/p^∞}))` (Yuan, Lemma 1.2). Let `F/ℚ_p` be a finite totally
ramified extension with ring of integers `𝒪_F`, maximal ideal `𝔪_F` and absolute ramification
index `e = v_F(p)`, which is `[F : ℚ_p]`. For a uniformizer `u` of `X` and `g ∈ Gal(K_FT/ℚ_p)`
let `f_{g,u} ∈ 𝔽_p⟦T⟧` be the coordinate series with `ev_u(f_{g,u}) = g(u)`.

Yuan, Proposition 1.3: there are no `P, F_τ, F_δ ∈ (𝒪_F ⧸ 𝔪_F ^ (e + 1))((T))` with reductions
`P̄ = T^p`, `F̄_τ = f_{τ,u}` and `F̄_δ = f_{δ,u}` such that `F_τ ∘ P = P ∘ F_τ` and
`F_δ ∘ P = P ∘ F_δ`. Reducing a lift modulo `𝔪_F ^ (e + 1)` gives Theorem A: the action of
`Gal(K_FT/ℚ_p)` on `X` is not `F`-liftable (Yuan, Definition 1.1). For `F = ℚ_p` (so `e = 1`)
a lift of Frobenius and a lift of `f_{τ,u}` commuting with it do not exist modulo `p ^ 2`.

Following Yuan, §6, both statements are instances of the obstructions of §3 and §4: the
ramification numbers of the iterates `τ^{p^k}` (Yuan, Proposition 5.1) exclude derivative level
`e` for `P` (case 1), and together with the order `p - 1` of the linear coefficient of `f_{δ,u}`
(Yuan, Lemma 5.3) they exclude every lower derivative level (case 2).

## Main results

* `FalseTateNonliftability.absoluteRamificationIdx_spectralIntegerRing`: `e = [F : ℚ_p]`.
* `FalseTateNonliftability.hasRamificationLimit_coordinateFamily_series_kummerGenerator`: the
  coordinate series of `τ` over the residue field of `F` has ramification limit
  `(p - 1)/(p + 1)` at `p` (Yuan, Proposition 5.1).
* `FalseTateNonliftability.not_finiteLiftable_falseTateExtension`,
  `FalseTateNonliftability.not_finiteLiftable_falseTate`: Yuan, Proposition 1.3, for every
  uniformizer `π` of `ℚ_p` and for `π = p`.
* `FalseTateNonliftability.not_finiteLiftable_falseTateExtension_of_orderOf`: Yuan,
  Proposition 1.3 with `δ` replaced by any `σ ∈ Gal(K_FT/ℚ_p(π^{1/p^∞}))` such that `χ(σ) mod p`
  has order `p - 1`, which includes every generator of the torsion subgroup of this group.
* `FalseTateNonliftability.not_isLiftable_falseTateExtension`,
  `FalseTateNonliftability.not_isLiftable_falseTate`: Yuan, Theorem A, for every uniformizer `π`
  of `ℚ_p` and for `π = p`.
* `FalseTateNonliftability.not_finiteLiftable_kummerGenerator_bot`: over `F = ℚ_p`, there is no
  lift of `f_{τ,u}` modulo `p ^ 2` commuting with a lift of Frobenius (Yuan, §6, case 1).

## Implementation notes

* The false Tate curve extension is `falseTateExtension p π` of FalseTateExtension, defined for
  every uniformizer `π` of `ℚ_p`; that `π` is a uniformizer is the instance
  `[Fact (Irreducible π)]`, as in FalseTateExtension. The extension `ℚ_p^FT` of Yuan is `π = p`.
* `F` is an intermediate field of `ℚ_p^alg/ℚ_p` with `[IsTotallyRamified ℚ_[p] F]`, which gives
  the same residue field condition of Definition 1.1 for `K = ℚ_p`.
* The index `e` is `absoluteRamificationIdx p 𝒪_F`, and finite lifts with index `r = e` live
  modulo `𝔪_F ^ (e + 1)`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Definition 1.1, Lemma 1.2, Proposition 1.3, Proposition 5.1, Lemma 5.3, §6 and Theorem A.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/

public section

open FontaineWintenberger FalseTateExtension PowerSeries
open IsLocalRing (ResidueField)
open scoped FalseTateExtension

namespace FalseTateNonliftability

/-- The absolute ramification index `e = v_F(p)` of a finite totally ramified extension `F/ℚ_p` is
`[F : ℚ_p]`. -/
theorem absoluteRamificationIdx_spectralIntegerRing (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsTotallyRamified ℚ_[p] F] :
    absoluteRamificationIdx p (spectralIntegerRing ℚ_[p] F) = Module.finrank ℚ_[p] F := by
  rw [← IsTotallyRamified.ramificationIdx_eq_finrank ℚ_[p] F, absoluteRamificationIdx,
    ← map_natCast (algebraMap 𝒪[ℚ_[p]] (spectralIntegerRing ℚ_[p] F)),
    ← ramificationIdx_eq_addVal_uniformizer _ _ (Fact.out : Irreducible (p : 𝒪[ℚ_[p]])),
    ENat.toNat_natCast]

variable (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)]

section Uniformizer

variable (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]
  (F : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] F]
  [IsTotallyRamified ℚ_[p] F] {u : FieldOfNorms ℚ_[p] (falseTateExtension p (π : ℚ_[p]))}
  (hu : FieldOfNorms.valuation ℚ_[p] (falseTateExtension p (π : ℚ_[p])) u =
    WithZero.exp (-1 : ℤ))

omit [FiniteDimensional ℚ_[p] F] in
/-- Yuan, Proposition 5.1, as used in §6: for a finite totally ramified extension `F/ℚ_p` and a
uniformizer `u` of `X_{ℚ_p}(K_FT)`, the coordinate series `f_{τ,u}` over the residue field of `F`
has ramification limit `(p - 1)/(p + 1)` at `p`: `f_{τ,u}'(0) = 1`, `τ` acts on `X_{ℚ_p}(K_FT)`
with infinite order, and the ramification numbers `d_k` of `τ^{p^k}` satisfy `d_k ≡ -1 (mod p)`,
`d_{k+1} ≥ (p + 1) d_k` and `d_k → (p - 1)/(p + 1)` in `ℤ_p`. -/
theorem hasRamificationLimit_coordinateFamily_series_kummerGenerator :
    ((IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p (π : ℚ_[p])) F u hu).series
      (τ p π).val).HasRamificationLimit p (kummerRamificationLimit p) := by
  have hd (k : ℕ) : (iterate ((IsLiftable.coordinateFamily p ℚ_[p]
      (falseTateExtension p (π : ℚ_[p])) F u hu).series (τ p π).val) (p ^ k)).ramificationNumber =
      kummerRamificationBreak p k := by
    rw [← CoordinateFamily.series_pow, IsLiftable.ramificationNumber_coordinateFamily_series,
      ramificationNumber_eq_of_order_sub_X_eq
        (order_coordinateSeries_kummerGenerator_pow_sub_X u hu k)]
    push_cast
    ring
  refine ⟨⟨?_, ?_, fun k ↦ ?_, fun k ↦ ?_⟩, ?_⟩
  · rw [IsLiftable.coeff_one_coordinateFamily_series_eq_one_iff]
    exact coeff_one_coordinateSeries_kummerGenerator u hu
  · rw [IsLiftable.isOfFinOrder_substEquiv_coordinateFamily_series_iff,
      FieldOfNorms.isOfFinOrder_substEquiv_coordinateSeries_iff]
    rintro ⟨n, hn, h⟩
    exact coordinateSeries_kummerGenerator_pow_ne_X u hu hn h
  · rw [hd]
    exact_mod_cast kummerRamificationBreak_succ_dvd p k
  · rw [hd, hd]
    exact_mod_cast kummerRamificationBreak_growth p k (Fact.out : p.Prime).two_le
  · simp_rw [hd, Int.cast_natCast]
    exact kummerRamificationBreak_tendsto_padic p

/-- Yuan, Proposition 1.3, for a uniformizer `π` of `ℚ_p` and every `σ ∈ Gal(K_FT/K_Kum)` such
that `χ(σ) mod p` has order `p - 1` in `𝔽_pˣ`, for instance every generator of the torsion
subgroup of `Gal(K_FT/K_Kum)` (the elements `δ` of Yuan, Lemma 1.2 (3)): let `F/ℚ_p` be a finite
totally ramified extension with absolute ramification index `e`, and let `u` be a uniformizer of
`X_{ℚ_p}(K_FT)`, `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})`. There are no
`P, F_τ, F_σ ∈ (𝒪_F ⧸ 𝔪_F ^ (e + 1))((T))` with reductions `P̄ = T^p`, `F̄_τ = f_{τ,u}` and
`F̄_σ = f_{σ,u}` such that `F_τ ∘ P = P ∘ F_τ` and `F_σ ∘ P = P ∘ F_σ`. -/
theorem not_finiteLiftable_falseTateExtension_of_orderOf
    {σ : falseTateKummerFixing p (π : ℚ_[p])}
    (hσ : orderOf (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom
      (padicCyclotomicCharacter p (π : ℚ_[p]) σ.val)) = p - 1) :
    ¬ CoordinateFamily.FiniteLiftable
      (IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p (π : ℚ_[p])) F u hu)
      {(τ p π).val, σ.val} (absoluteRamificationIdx p (spectralIntegerRing ℚ_[p] F)) := by
  rintro ⟨L⟩
  have hτ : (τ p π).val ∈ ({(τ p π).val, σ.val} : Set _) := Set.mem_insert _ _
  have hσ' : σ.val ∈ ({(τ p π).val, σ.val} : Set _) := Set.mem_insert_of_mem _ rfl
  have hP := L.residue_frobenius
  rw [(Fact.out : Nat.card (ResidueField (spectralIntegerRing ℚ_[p] F)) = p)] at hP
  refine Truncation.false_of_commute p hP (L.residue_lift ⟨_, hτ⟩) (L.residue_lift ⟨_, hσ'⟩)
    (L.commute ⟨_, hτ⟩) (L.commute ⟨_, hσ'⟩)
    (hasRamificationLimit_coordinateFamily_series_kummerGenerator p π F hu)
    (kummerRamificationLimit_notMem_range_intCast p)
    (CoordinateFamily.constantCoeff_series _ _) ?_
  rw [IsLiftable.orderOf_coeff_one_coordinateFamily_series]
  exact orderOf_coeff_one_coordinateSeries_falseTateKummerFixing u hu hσ

/-- **Yuan, Proposition 1.3**, for a uniformizer `π` of `ℚ_p`: let `F/ℚ_p` be a finite totally
ramified extension with absolute ramification index `e`, and let `u` be a uniformizer of
`X_{ℚ_p}(K_FT)`, `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})`. There are no
`P, F_τ, F_δ ∈ (𝒪_F ⧸ 𝔪_F ^ (e + 1))((T))` with reductions `P̄ = T^p`, `F̄_τ = f_{τ,u}` and
`F̄_δ = f_{δ,u}` such that `F_τ ∘ P = P ∘ F_τ` and `F_δ ∘ P = P ∘ F_δ`. -/
theorem not_finiteLiftable_falseTateExtension :
    ¬ CoordinateFamily.FiniteLiftable
      (IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p (π : ℚ_[p])) F u hu)
      {(τ p π).val, (δ p π).val} (absoluteRamificationIdx p (spectralIntegerRing ℚ_[p] F)) :=
  not_finiteLiftable_falseTateExtension_of_orderOf p π F hu
    (orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator p π)

/-- **Yuan, Theorem A**, for a uniformizer `π` of `ℚ_p`: for every finite totally ramified
extension `F/ℚ_p`, the action of `Gal(K_FT/ℚ_p)` on the field of norms `X_{ℚ_p}(K_FT)` of
`K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` is not `F`-liftable (Yuan, Definition 1.1). -/
theorem not_isLiftable_falseTateExtension :
    ¬ IsLiftable p ℚ_[p] (falseTateExtension p (π : ℚ_[p])) F := fun h ↦
  not_finiteLiftable_falseTateExtension p π F (FieldOfNorms.valuation_uniformizer _ _)
    (h.finiteLiftable _ _ _)

/-- Yuan, §6 (proof of Proposition 1.3, case 1): over `F = ℚ_p`, for a uniformizer `u` of
`X_{ℚ_p}(K_FT)`, there are no `P, F_τ ∈ (ℤ_p ⧸ p ^ 2)((T))` with reductions `P̄ = T^p` and
`F̄_τ = f_{τ,u}` such that `F_τ ∘ P = P ∘ F_τ`. -/
theorem not_finiteLiftable_kummerGenerator_bot :
    ¬ CoordinateFamily.FiniteLiftable
      (IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p (π : ℚ_[p])) ⊥ u hu)
      {(τ p π).val} 1 := by
  have he : absoluteRamificationIdx p
      (spectralIntegerRing ℚ_[p] (⊥ : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))) = 1 := by
    rw [absoluteRamificationIdx_spectralIntegerRing, IntermediateField.finrank_bot]
  intro h
  rw [← he] at h
  obtain ⟨L⟩ := h
  have hτ : (τ p π).val ∈ ({(τ p π).val} : Set _) := rfl
  have hP := L.residue_frobenius
  rw [(Fact.out : Nat.card (ResidueField (spectralIntegerRing ℚ_[p]
    (⊥ : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])))) = p)] at hP
  have hlt := Truncation.derivativeLevel_lt_absoluteRamificationIdx p hP (L.residue_lift ⟨_, hτ⟩)
    (L.commute ⟨_, hτ⟩)
    (hasRamificationLimit_coordinateFamily_series_kummerGenerator p π ⊥ hu).toHasRamificationGrowth
  have hle := Truncation.one_le_derivativeLevel p hP
  omega

end Uniformizer

variable (F : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] F]
  [IsTotallyRamified ℚ_[p] F]

/-- **Yuan, Proposition 1.3**: let `F/ℚ_p` be a finite totally ramified extension with absolute
ramification index `e`, and let `u` be a uniformizer of the field of norms `X_{ℚ_p}(ℚ_p^FT)` of
the false Tate curve extension `ℚ_p^FT = ℚ_p(p^{1/p^∞}, ζ_{p^∞})`. There are no
`P, F_τ, F_δ ∈ (𝒪_F ⧸ 𝔪_F ^ (e + 1))((T))` with reductions `P̄ = T^p`, `F̄_τ = f_{τ,u}` and
`F̄_δ = f_{δ,u}` such that `F_τ ∘ P = P ∘ F_τ` and `F_δ ∘ P = P ∘ F_δ`. -/
theorem not_finiteLiftable_falseTate
    {u : FieldOfNorms ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p]))}
    (hu : FieldOfNorms.valuation ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) u =
      WithZero.exp (-1 : ℤ)) :
    ¬ CoordinateFamily.FiniteLiftable
      (IsLiftable.coordinateFamily p ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) F u hu)
      {(τ p (p : 𝒪[ℚ_[p]])).val, (δ p (p : 𝒪[ℚ_[p]])).val}
      (absoluteRamificationIdx p (spectralIntegerRing ℚ_[p] F)) :=
  not_finiteLiftable_falseTateExtension p (p : 𝒪[ℚ_[p]]) F hu

/-- **Theorem A** (Yuan): let `p ≥ 3`. For every finite totally ramified extension `F/ℚ_p`, the
action of `Gal(ℚ_p^FT/ℚ_p)` on the field of norms `X_{ℚ_p}(ℚ_p^FT)` of the false Tate curve
extension `ℚ_p^FT = ℚ_p(p^{1/p^∞}, ζ_{p^∞})` is not `F`-liftable (Yuan, Definition 1.1). -/
theorem not_isLiftable_falseTate :
    ¬ IsLiftable p ℚ_[p] (falseTateExtension p ((p : 𝒪[ℚ_[p]]) : ℚ_[p])) F :=
  not_isLiftable_falseTateExtension p (p : 𝒪[ℚ_[p]]) F

end FalseTateNonliftability
