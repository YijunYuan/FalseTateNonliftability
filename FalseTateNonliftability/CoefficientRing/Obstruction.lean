/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative
public import FalseTateNonliftability.Differential.ExactDifferentialLimit
public import FalseTateNonliftability.Differential.InvariantExactDifferential
public import FalseTateNonliftability.LaurentSeries.NormalForm

/-!
# The two obstructions to commuting lifts modulo `𝔪 ^ (e + 1)`

Let `κ` be a field and `p` a prime. A power series `f ∈ κ⟦T⟧` has ramification growth at `p` if
`f = T + O(T²)`, the automorphism `a ↦ a ∘ f` of `κ((T))` has infinite order, and the
ramification numbers `d_k = v_T(f^{∘p^k} - T) - 1` satisfy `d_k ≡ -1 (mod p)` and
`d_{k+1} ≥ (p + 1) d_k` for every `k ≥ 0`. For the coordinate series of the Kummer generator `τ`
on the field of norms of the false Tate curve extension these are Yuan, Proposition 5.1.

Let `O` be a discrete valuation ring with residue field `κ = 𝔽_p`, `p ≠ 0` in `O`, and let
`e = v(p)` be its absolute ramification index. Let `P, G ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` with
`G ∘ P = P ∘ G`, where `P` reduces to `T ^ p`.

1. If `G` reduces to a power series `f` with ramification growth at `p`, then the derivative level
   of `P` satisfies `s(P) < e` (Yuan, §6, proof of Proposition 1.3, case 1).
2. Let `G` reduce to a power series `f = T + O(T²)` such that `a ↦ a ∘ f` has infinite order and
   the ramification numbers `d_k` converge in `ℤ_p` to some `b ∉ ℤ`, and let
   `D ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` with `D ∘ P = P ∘ D` reduce to a power series `g ∈ T κ⟦T⟧` whose
   linear coefficient has multiplicative order `p - 1`. Then `s(P) ≥ e` (Yuan, §6, proof of
   Proposition 1.3, case 2). Indeed, if `s(P) < e`, then `a ↦ a ∘ f` fixes a nonzero exact
   differential (Yuan, Lemma 4.1), and then `b ∈ ℤ` (Yuan, Proposition 4.3).

If `f` satisfies the hypotheses of both cases, such `P, G, D` do not exist. For the coordinate
series of the Kummer generator `τ` and of the tame generator `δ` of the false Tate curve extension
this is Yuan, Proposition 1.3.

## Main definitions

* `PowerSeries.HasRamificationGrowth p f`: `f` has ramification growth at `p`.
* `PowerSeries.HasRamificationLimit p f b`: `f` has ramification growth at `p` and its ramification
  numbers converge to `b` in `ℤ_p`.

## Main results

* `LaurentSeries.isAdmissible_of_mapRingHom_eq_ofPowerSeries`: a Laurent series whose image
  under a coefficient map is a power series `f` with `f(0) = 0` and `f'(0)` a unit is admissible.
* `FalseTateNonliftability.Truncation.derivativeLevel_lt_absoluteRamificationIdx`: `s(P) < e`.
* `FalseTateNonliftability.Truncation.absoluteRamificationIdx_le_derivativeLevel`: `s(P) ≥ e`.
* `FalseTateNonliftability.Truncation.false_of_commute`: there are no `P, G, D` as above when
  `f` has ramification growth at `p`.

## References

* Yuan, Lemma 2.4, Theorem 3.1, Theorem 3.4, Lemma 4.1, Proposition 4.3, Proposition 5.1 and §6
  (proof of Proposition 1.3).
-/

@[expose] public section

noncomputable section

/-! ### The obstruction at derivative level `e` -/

section TopLevel

open Filter
open IsLocalRing (ResidueField)
open scoped PowerSeries

namespace PowerSeries

variable {κ : Type*} [Field κ]

/-- A power series `f` over a field `κ` has ramification growth at `p` if `f'(0) = 1`, the
automorphism `a ↦ a ∘ f` of `κ((T))` has infinite order (so `f = T + O(T²)`), and the
ramification numbers `d_k = v_T(f^{∘p^k} - T) - 1` satisfy `d_k ≡ -1 (mod p)` and
`d_{k+1} ≥ (p + 1) d_k` for every `k ≥ 0` (for the Kummer generator of the false Tate curve
extension: Yuan, Proposition 5.1). -/
structure HasRamificationGrowth (p : ℕ) (f : κ⟦X⟧) : Prop where
  /-- `f'(0) = 1`. -/
  coeff_one : f.coeff 1 = 1
  /-- `a ↦ a ∘ f` has infinite order. -/
  not_isOfFinOrder : ¬ IsOfFinOrder (LaurentSeries.substEquiv f)
  /-- `d_k ≡ -1 (mod p)`. -/
  dvd_ramificationNumber_add_one (k : ℕ) : (p : ℤ) ∣ (iterate f (p ^ k)).ramificationNumber + 1
  /-- `d_{k+1} ≥ (p + 1) d_k`. -/
  mul_ramificationNumber_le (k : ℕ) :
    ((p : ℤ) + 1) * (iterate f (p ^ k)).ramificationNumber ≤
      (iterate f (p ^ (k + 1))).ramificationNumber

end PowerSeries

namespace LaurentSeries

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [CommRing S]
  [IsLocalRing S]

/-- A Laurent series `G` whose image under a coefficient map is a power series `f` with
`f(0) = 0` and `f'(0)` a unit is admissible. -/
theorem isAdmissible_of_mapRingHom_eq_ofPowerSeries (φ : R →+* S) {G : LaurentSeries R}
    {f : PowerSeries S} (hf : f.constantCoeff = 0) (hf' : IsUnit (f.coeff 1))
    (hG : mapRingHom φ G = HahnSeries.ofPowerSeries ℤ S f) : IsAdmissible G :=
  (isAdmissible_mapRingHom_iff φ G).mp (hG ▸ isAdmissible_ofPowerSeries hf hf')

variable [IsPrincipalIdealRing R] [IsArtinianRing S] [IsPrincipalIdealRing S]

/-- If the image of `G` under a coefficient map is a power series `f` with `f(0) = 0` and
`f'(0)` a unit, then the image of the iterate `G^{∘n}` is `f^{∘n}`. -/
private theorem mapRingHom_iterate_eq_ofPowerSeries_iterate (φ : R →+* S) {G : LaurentSeries R}
    {f : PowerSeries S} (hf : f.constantCoeff = 0)
    (hf' : IsUnit (f.coeff 1)) (hres : mapRingHom φ G = HahnSeries.ofPowerSeries ℤ S f) (n : ℕ) :
    mapRingHom φ ((subst G)^[n] (HahnSeries.single (1 : ℤ) 1)) =
      HahnSeries.ofPowerSeries ℤ S (PowerSeries.iterate f n) := by
  have hsubst : ⇑(subst (HahnSeries.ofPowerSeries ℤ S f)) = substEquiv f :=
    funext fun x ↦ (substEquiv_apply hf hf' x).symm
  rw [mapRingHom_subst_iterate φ G, hres, hsubst, mapRingHom_single, map_one,
    ofPowerSeries_iterate hf hf']

/-- If `G ∘ P = P ∘ G` for admissible `P` and `G`, then `G^{∘n} ∘ P = P ∘ G^{∘n}`. -/
private theorem subst_iterate_comm {P G : LaurentSeries R} (hP : IsAdmissible P)
    (hG : IsAdmissible G) (hcomm : subst P G = subst G P) (n : ℕ) :
    subst P ((subst G)^[n] (HahnSeries.single (1 : ℤ) 1)) =
      subst ((subst G)^[n] (HahnSeries.single (1 : ℤ) 1)) P := by
  rw [(subst_commute hP hG hcomm).iterate_right n, subst_X hP, subst_iterate hG]

end LaurentSeries

namespace FalseTateNonliftability.Truncation

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (p : ℕ) [Fact p.Prime] [Fact (Nat.card (ResidueField O) = p)] [NeZero (p : O)]

/-- Yuan, §6, proof of Proposition 1.3, case 1: let `p ≠ 0` in `O`, let `κ = 𝔽_p` and `e = v(p)`.
Let `P, G ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` with `G ∘ P = P ∘ G`, where `P` reduces to `T ^ p` and `G`
reduces to a power series `f` with ramification growth at `p`. Then the derivative level of `P`
satisfies `s(P) < e`. -/
theorem derivativeLevel_lt_absoluteRamificationIdx
    {P G : LaurentSeries (Truncation O (absoluteRamificationIdx p O))}
    {f : PowerSeries (ResidueField O)}
    (hP : mapRingHom (residue O _) P = HahnSeries.single (p : ℤ) 1)
    (hG : mapRingHom (residue O _) G = HahnSeries.ofPowerSeries ℤ _ f)
    (hcomm : subst P G = subst G P) (hf : f.HasRamificationGrowth p) :
    derivativeLevel P < absoluteRamificationIdx p O := by
  have := charP_of_natCard_eq_prime (Fact.out : Nat.card (ResidueField O) = p)
  obtain ⟨hf0, hf'⟩ := constantCoeff_eq_zero_and_isUnit_of_not_isOfFinOrder hf.not_isOfFinOrder
  refine lt_of_le_of_ne (derivativeLevel_le P) fun hs ↦ ?_
  have hPadm := isAdmissible_of_mapRingHom_residue_eq p hP
  have hGadm := isAdmissible_of_mapRingHom_eq_ofPowerSeries _ hf0 hf' hG
  obtain ⟨k, hk⟩ := (tendsto_atTop.mp (PowerSeries.tendsto_ramificationNumber_iterate_pow_atTop p
    hf.coeff_one hf.not_isOfFinOrder) ((p : ℤ) - (normalizedDerivative P).order)).exists
  have hd := PowerSeries.one_le_ramificationNumber_iterate hf.coeff_one hf.not_isOfFinOrder
    (pow_pos (Fact.out : p.Prime).pos k)
  have hnext : ((p : ℤ) + 1) * (PowerSeries.iterate f (p ^ k)).ramificationNumber ≤
      (PowerSeries.iterate (PowerSeries.iterate f (p ^ k)) p).ramificationNumber := by
    rw [← PowerSeries.iterate_mul (.of_constantCoeff_zero' hf0), ← pow_succ]
    exact hf.mul_ramificationNumber_le k
  obtain ⟨w, hw, hw', α, hα, hnormal⟩ :=
    PowerSeries.exists_normalForm p (hf.dvd_ramificationNumber_add_one k) hnext
  obtain ⟨H, hH, hH', hHw⟩ := exists_map_residue_eq _ w hw hw'
  have hconj := mapRingHom_conj_of_mapRingHom_eq _ hH hH' (hGadm.iterate (p ^ k))
    (PowerSeries.constantCoeff_iterate hf0 _)
    (mapRingHom_iterate_eq_ofPowerSeries_iterate _ hf0 hf' hG (p ^ k))
  rw [hHw] at hconj
  have hbound := order_normalizedDerivative_le p (mapRingHom_residue_conj p hP hH hH')
    ((conj_commute_iff hH hH' hPadm (hGadm.iterate (p ^ k))).mpr
      (subst_iterate_comm hPadm hGadm hcomm (p ^ k)))
    ((derivativeLevel_conj hPadm hH hH').trans hs) hd (hf.dvd_ramificationNumber_add_one k) hα
    (hconj ▸ hnormal)
  rw [order_normalizedDerivative_conj p hP hH hH'] at hbound
  omega

end FalseTateNonliftability.Truncation

end TopLevel

/-! ### The obstruction at lower derivative level and the finite obstruction -/

section LowerLevel

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

end LowerLevel
