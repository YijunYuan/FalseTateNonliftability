/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.TopLevelObstruction
public import FalseTateNonliftability.LaurentSeries.InvariantExactDifferential
public import FalseTateNonliftability.LaurentSeries.ExactDifferentialLimit

/-!
# The obstruction at lower derivative level and the finite obstruction

Let `O` be a discrete valuation ring with residue field `κ = 𝔽_p`, `p ≠ 0` in `O`, and let
`e = v(p)` be its absolute ramification index. Let `P, G, D ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` with
`G ∘ P = P ∘ G` and `D ∘ P = P ∘ D`, where `P` reduces to `T ^ p`, `G` reduces to a power series
`f = T + O(T²)` such that `a ↦ a ∘ f` has infinite order and the ramification numbers
`d_k = v_T(f^{∘p^k} - T) - 1` converge in `ℤ_p` to some `b ∉ ℤ`, and `D` reduces to a power
series `g ∈ T κ⟦T⟧` whose linear coefficient has multiplicative order `p - 1`. Then the derivative
level of `P` satisfies `s(P) ≥ e` (Yuan, §6, proof of Proposition 1.3, case 2). Indeed, if
`s(P) < e`, then `a ↦ a ∘ f` fixes a nonzero exact differential (Yuan, Lemma 4.1), and then
`b ∈ ℤ` (Yuan, Proposition 4.3).

If moreover `f` has ramification growth at `p`, then `s(P) < e` by the obstruction at derivative
level `e`, so such `P, G, D` do not exist. For the coordinate series of the Kummer generator `τ`
and of the tame generator `δ` of the false Tate curve extension this is Yuan, Proposition 1.3.

## Main definitions

* `PowerSeries.HasRamificationLimit p f b`: `f` has ramification growth at `p` and its ramification
  numbers converge to `b` in `ℤ_p`.

## Main results

* `FalseTateNonliftability.Truncation.absoluteRamificationIdx_le_derivativeLevel`: `s(P) ≥ e`.
* `FalseTateNonliftability.Truncation.false_of_commute`: there are no `P, G, D` as above when
  `f` has ramification growth at `p`.

## References

* Yuan, Lemma 2.4, Lemma 4.1, Proposition 4.3 and §6 (proof of Proposition 1.3).
-/

@[expose] public section

noncomputable section

open Filter Topology
open IsLocalRing (ResidueField)
open scoped PowerSeries

namespace PowerSeries

variable {κ : Type*} [Field κ]

/-- A power series `f` over a field `κ` has ramification limit `b ∈ ℤ_p` at `p` if it has
ramification growth at `p` and its ramification numbers `d_k = v_T(f^{∘p^k} - T) - 1` converge
to `b` in `ℤ_p` (for the Kummer generator of the false Tate curve extension,
`b = (p - 1)/(p + 1)`: Yuan, Proposition 5.1). -/
structure HasRamificationLimit (p : ℕ) [Fact p.Prime] (f : κ⟦X⟧) (b : ℤ_[p]) : Prop
    extends HasRamificationGrowth p f where
  /-- `d_k → b` in `ℤ_p`. -/
  tendsto_ramificationNumber :
    Tendsto (fun k : ℕ ↦ ((iterate f (p ^ k)).ramificationNumber : ℤ_[p])) atTop (𝓝 b)

end PowerSeries

namespace FalseTateNonliftability.Truncation

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (p : ℕ) [Fact p.Prime] [Fact (Nat.card (ResidueField O) = p)]

/-- Yuan, Lemma 2.4 (1): if `P` reduces to `T ^ p` and `G` commutes with `P` and reduces to a
power series `f` with `f(0) = 0` and `f'(0)` a unit, then `h_P ∘ f = (f')^(p - 1) h_P`. -/
private theorem substEquiv_normalizedDerivative_of_commute {r : ℕ}
    {P G : LaurentSeries (Truncation O r)} {f : PowerSeries (ResidueField O)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hG : mapRingHom (residue O r) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hf : f.constantCoeff = 0) (hf' : IsUnit (f.coeff 1)) (hcomm : subst P G = subst G P) :
    substEquiv f (normalizedDerivative P) =
      derivative (ResidueField O) (HahnSeries.ofPowerSeries ℤ _ f) ^ (p - 1) *
        normalizedDerivative P := by
  have h1 : (mapRingHom (residue O r) G).coeff 1 ≠ 0 := by
    rw [hG]
    simpa only [show (1 : ℤ) = (1 : ℕ) from rfl, HahnSeries.ofPowerSeries_apply_coeff]
      using hf'.ne_zero
  have h := subst_normalizedDerivative_of_commute p hP
    (isAdmissible_of_mapRingHom_eq_ofPowerSeries _ hf hf' hG) h1 hcomm
  rwa [hG, ← substEquiv_apply hf hf'] at h

variable [NeZero (p : O)]

/-- Yuan, §6, proof of Proposition 1.3, case 2: let `p ≠ 0` in `O`, let `κ = 𝔽_p` and `e = v(p)`.
Let `P, G, D ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` with `G ∘ P = P ∘ G` and `D ∘ P = P ∘ D`, where `P`
reduces to `T ^ p`, `G` reduces to a power series `f` with `f'(0) = 1` such that `a ↦ a ∘ f` has
infinite order and the ramification numbers `d_k = v_T(f^{∘p^k} - T) - 1` converge in `ℤ_p` to
some `b ∉ ℤ`, and `D` reduces to a power series `g ∈ T κ⟦T⟧` whose linear coefficient has
multiplicative order `p - 1`. Then the derivative level of `P` satisfies `s(P) ≥ e`. -/
theorem absoluteRamificationIdx_le_derivativeLevel
    {P G D : LaurentSeries (Truncation O (absoluteRamificationIdx p O))}
    {f g : PowerSeries (ResidueField O)} {b : ℤ_[p]}
    (hP : mapRingHom (residue O _) P = HahnSeries.single (p : ℤ) 1)
    (hG : mapRingHom (residue O _) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hD : mapRingHom (residue O _) D = HahnSeries.ofPowerSeries ℤ _ g)
    (hcommG : subst P G = subst G P) (hcommD : subst P D = subst D P)
    (hf1 : f.coeff 1 = 1) (hf : ¬ IsOfFinOrder (substEquiv f))
    (hlimit : Tendsto (fun k : ℕ ↦ ((PowerSeries.iterate f (p ^ k)).ramificationNumber : ℤ_[p]))
      atTop (𝓝 b))
    (hb : b ∉ Set.range (Int.cast : ℤ → ℤ_[p]))
    (hg : g.constantCoeff = 0) (hg1 : orderOf (g.coeff 1) = p - 1) :
    absoluteRamificationIdx p O ≤ derivativeLevel P := by
  have hκ : Nat.card (ResidueField O) = p := Fact.out
  have := charP_of_natCard_eq_prime hκ
  have : Finite (ResidueField O) :=
    Nat.finite_of_card_ne_zero (hκ ▸ (Fact.out : p.Prime).ne_zero)
  by_contra! hs
  obtain ⟨hf0, hf'⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf
  have hg' : IsUnit (g.coeff 1) :=
    (orderOf_pos_iff.mp (hg1 ▸ Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)).isUnit
  obtain ⟨A, hA⟩ := exists_normalizedDerivative_eq_derivative p hs
  obtain ⟨a, B, ha, hB, hinv⟩ := exists_exact_invariant_of_weighted_identities p hf0 hf1 hg hg1
    (normalizedDerivative_ne_zero (derivative_ne_zero p hP)) hA.symm
    (substEquiv_normalizedDerivative_of_commute p hP hG hf0 hf' hcommG)
    (substEquiv_normalizedDerivative_of_commute p hP hD hg hg' hcommD)
  refine hb ⟨-(a.order + 1), ?_⟩
  rw [padic_ramification_limit_eq_of_invariant_exact_differential p hf1 hf hlimit ha ⟨B, hB⟩ hinv,
    Int.cast_neg]

/-- Yuan, §6, proof of Proposition 1.3: let `p ≠ 0` in `O`, let `κ = 𝔽_p` and `e = v(p)`. Let
`f ∈ κ⟦T⟧` have ramification limit `b ∉ ℤ` at `p`, and let `g ∈ T κ⟦T⟧` have linear
coefficient of multiplicative order `p - 1`. Then there are no
`P, G, D ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` reducing to `T ^ p`, `f` and `g` with `G ∘ P = P ∘ G` and
`D ∘ P = P ∘ D`. -/
theorem false_of_commute
    {P G D : LaurentSeries (Truncation O (absoluteRamificationIdx p O))}
    {f g : PowerSeries (ResidueField O)} {b : ℤ_[p]}
    (hP : mapRingHom (residue O _) P = HahnSeries.single (p : ℤ) 1)
    (hG : mapRingHom (residue O _) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hD : mapRingHom (residue O _) D = HahnSeries.ofPowerSeries ℤ _ g)
    (hcommG : subst P G = subst G P) (hcommD : subst P D = subst D P)
    (hf : f.HasRamificationLimit p b) (hb : b ∉ Set.range (Int.cast : ℤ → ℤ_[p]))
    (hg : g.constantCoeff = 0) (hg1 : orderOf (g.coeff 1) = p - 1) : False :=
  (derivativeLevel_lt_absoluteRamificationIdx p hP hG hcommG hf.toHasRamificationGrowth).not_ge
    (absoluteRamificationIdx_le_derivativeLevel p hP hG hD hcommG hcommD hf.coeff_one
      hf.not_isOfFinOrder hf.tendsto_ramificationNumber hb hg hg1)

end FalseTateNonliftability.Truncation
