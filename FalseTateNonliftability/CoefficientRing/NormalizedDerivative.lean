/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.Mathlib.Algebra.CharP.CharAndCard
public import FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Derivative

/-!
# The derivative level, the normalized derivative and its valuation bound

Let `O` be a discrete valuation ring with maximal ideal `𝔪` and residue field `κ`, let `p` be a
prime with `p ≠ 0` in `O` and `κ = 𝔽_p`, and let `e = v(p)` be the absolute ramification index
of `O`. In `R_r = (O ⧸ 𝔪 ^ (r + 1))((T))` let `Λ_j = 𝔪 ^ j R_r`. The derivative level `s(P)` of
`P ∈ R_r` is the least `s` with `P' ∉ Λ_{s + 1}`, and the normalized derivative of `P` is the
layer `h_P = ϖ⁻ˢ P' ∈ κ((T))` of `P'` in `Λ_s ⧸ Λ_{s + 1} ≃ κ((T))` (Yuan, Definition 2.5).

Let `P ∈ R_e` reduce to `T ^ p`. Then `P' ≠ 0`, and `s = s(P)` is the unique integer with
`P' ∈ Λ_s ∖ Λ_{s + 1}`; it satisfies `1 ≤ s ≤ e`. By Yuan, Lemma 2.4:

1. if `G ∈ R_e` commutes with `P` and its reduction `f` lies in `T κ⟦T⟧` and has nonzero linear
   coefficient, then `h_P ∘ f = (f')^(p - 1) h_P`;
2. if `H` is a power series over `O ⧸ 𝔪 ^ (e + 1)` with `H(0) = 0` and `H'(0)` a unit, with
   reduction `H̄`, then `P_H = H ∘ P ∘ H^{∘-1}` reduces to `T ^ p`, `s(P_H) = s(P)`,
   `h_{P_H} ∘ H̄ = (H̄')^(p - 1) h_P` and `v_T(h_{P_H}) = v_T(h_P)`;
3. if `s < e`, then `h_P = A'` for some `A ∈ κ((T))`; if `s = e`, then
   `h_P = c T^(p - 1) + A'` for some `c ∈ κˣ` and `A ∈ κ((T))`, and hence `h_P' ≠ 0` and
   `v_T(h_P') ≤ p - 2`.

Except for `P' ≠ 0` and `1 ≤ s(P)`, these statements are proved over every truncation `R_r`.

Let `k` be a field of characteristic `p`, let `d ≥ 1` with `d ≡ -1 (mod p)`, and let
`g = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ∈ kˣ`. If `h ∈ k((T))` satisfies
`h ∘ g = (g')^(p - 1) h`, `h' ≠ 0` and `v_T(h') ≤ p - 2`, then `v_T(h) ≤ p - 1 - d`. Hence, if
`P, G ∈ R_r` commute, `P` reduces to `T ^ p`, `s(P) = e`, and the reduction `f` of `G` satisfies
`f = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ∈ κˣ`, `d ≥ 1` and `d ≡ -1 (mod p)`, then
`v_T(h_P) ≤ p - 1 - d` (Yuan, Theorem 3.1, where `r = e`).

## Main definitions

* `absoluteRamificationIdx p O`: the absolute ramification index `e = v(p)` of `O`.
* `Truncation.derivativeLevel P`: the derivative level `s(P)`.
* `Truncation.normalizedDerivative P`: the normalized derivative `h_P`.

## Main results

* `Truncation.derivative_ne_zero`, `Truncation.one_le_derivativeLevel`,
  `Truncation.derivativeLevel_le`, `Truncation.derivativeLevel_eq_iff`: the derivative level.
* `Truncation.subst_normalizedDerivative_of_commute`: Lemma 2.4 (1).
* `Truncation.mapRingHom_residue_conj`, `Truncation.derivativeLevel_conj`,
  `Truncation.subst_normalizedDerivative_conj`, `Truncation.order_normalizedDerivative_conj`:
  Lemma 2.4 (2).
* `Truncation.exists_normalizedDerivative_eq_derivative`,
  `Truncation.exists_normalizedDerivative_eq_single_add_derivative`,
  `Truncation.derivative_normalizedDerivative_ne_zero`,
  `Truncation.order_derivative_normalizedDerivative_le`: Lemma 2.4 (3).
* `LaurentSeries.order_le_of_subst_eq_derivative_pow_mul`: the bound `v_T(h) ≤ p - 1 - d` over a
  field of characteristic `p`.
* `Truncation.order_normalizedDerivative_le`: Yuan, Theorem 3.1.

## Implementation details

The isomorphism `Λ_s ⧸ Λ_{s + 1} ≃ κ((T))` is multiplication by `ϖ ^ s` for a uniformizer `ϖ` of
`O` fixed in `Truncation.gradedLayerEquiv`; another uniformizer multiplies `h_P` by a nonzero
constant. The residue field hypothesis `κ = 𝔽_p` is the instance argument
`[Fact (Nat.card (ResidueField O) = p)]`; `charP_of_natCard_eq_prime` gives
`CharP (ResidueField O) p`.

## References

* Yuan, Lemma 2.4, Definition 2.5 and Theorem 3.1.
-/

@[expose] public section

noncomputable section

/-! ### The derivative level and the normalized derivative -/

section NormalizedDerivative

open PowerSeries (constantCoeff_map_eq_zero isUnit_coeff_one_map)

open IsLocalRing (maximalIdeal ResidueField)

namespace FalseTateNonliftability

open LaurentSeries

/-- The absolute ramification index `e = v(p)` of a discrete valuation ring `O`, where `v` is the
normalized valuation of `O`; it is `0` if `p = 0` in `O`. -/
def absoluteRamificationIdx (p : ℕ) (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : ℕ :=
  (IsDiscreteValuationRing.addVal O (p : O)).toNat

section AbsoluteRamificationIdx

variable (p : ℕ) {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem exists_natCast_eq_unit_mul_pow (hp : (p : O) ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : Oˣ, (p : O) = u * ϖ ^ absoluteRamificationIdx p O := by
  obtain ⟨n, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp hϖ
  rw [absoluteRamificationIdx, IsDiscreteValuationRing.addVal_def _ u hϖ n hpu,
    ENat.toNat_natCast]
  exact ⟨u, hpu⟩

/-- `p ∈ 𝔪 ^ e`. -/
theorem natCast_mem_maximalIdeal_pow_absoluteRamificationIdx :
    (p : O) ∈ maximalIdeal O ^ absoluteRamificationIdx p O := by
  by_cases hp : (p : O) = 0
  · rw [hp]
    exact zero_mem _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := exists_natCast_eq_unit_mul_pow p hp hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu]
  exact dvd_mul_left _ _

/-- `p ∉ 𝔪 ^ (e + 1)` if `p ≠ 0` in `O`. -/
theorem natCast_notMem_maximalIdeal_pow_absoluteRamificationIdx_add_one [NeZero (p : O)] :
    (p : O) ∉ maximalIdeal O ^ (absoluteRamificationIdx p O + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := exists_natCast_eq_unit_mul_pow p (NeZero.ne _) hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu, pow_succ,
    mul_comm (u : O), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
  exact fun h ↦ hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)

end AbsoluteRamificationIdx

namespace Truncation

section LocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {r : ℕ}

/-- The derivative level `s(P)` of `P ∈ (O ⧸ 𝔪 ^ (r + 1))((T))`: the least `s` such that
`P' ∉ Λ_{s + 1}`; it is `0` if `P' = 0` (Yuan, Definition 2.5). -/
def derivativeLevel (P : LaurentSeries (Truncation O r)) : ℕ :=
  sInf {s | derivative (Truncation O r) P ∉ layerIdeal O r (s + 1)}

/-- `P' ∈ Λ_{s(P)}`. -/
theorem derivative_mem_layerIdeal_derivativeLevel (P : LaurentSeries (Truncation O r)) :
    derivative (Truncation O r) P ∈ layerIdeal O r (derivativeLevel P) := by
  cases h : derivativeLevel P with
  | zero =>
    rw [layerIdeal_zero]
    exact Submodule.mem_top
  | succ s =>
    have hs : s < derivativeLevel P := by omega
    simpa using Nat.notMem_of_lt_sInf hs

/-- `P' ∉ Λ_{s(P) + 1}` if `P' ≠ 0`. -/
theorem derivative_notMem_layerIdeal_derivativeLevel_add_one {P : LaurentSeries (Truncation O r)}
    (h : derivative (Truncation O r) P ≠ 0) :
    derivative (Truncation O r) P ∉ layerIdeal O r (derivativeLevel P + 1) :=
  Nat.sInf_mem (s := {s | derivative (Truncation O r) P ∉ layerIdeal O r (s + 1)})
    ⟨r, by rwa [Set.mem_ofPred_eq, layerIdeal_eq_bot O (Nat.lt_succ_self r), Ideal.mem_bot]⟩

/-- `s(P) ≤ r`. -/
theorem derivativeLevel_le (P : LaurentSeries (Truncation O r)) : derivativeLevel P ≤ r := by
  by_cases h : derivative (Truncation O r) P = 0
  · simp [derivativeLevel, h]
  · exact Nat.sInf_le (by
      rwa [Set.mem_ofPred_eq, layerIdeal_eq_bot O (Nat.lt_succ_self r), Ideal.mem_bot])

/-- If `P' ≠ 0`, then `s(P)` is the unique `s` with `P' ∈ Λ_s ∖ Λ_{s + 1}` (Yuan, Lemma 2.4). -/
theorem derivativeLevel_eq_iff {P : LaurentSeries (Truncation O r)}
    (h : derivative (Truncation O r) P ≠ 0) {s : ℕ} :
    derivativeLevel P = s ↔ derivative (Truncation O r) P ∈ layerIdeal O r s ∧
      derivative (Truncation O r) P ∉ layerIdeal O r (s + 1) := by
  constructor
  · rintro rfl
    exact ⟨derivative_mem_layerIdeal_derivativeLevel P,
      derivative_notMem_layerIdeal_derivativeLevel_add_one h⟩
  · rintro ⟨hs, hs1⟩
    refine le_antisymm (Nat.sInf_le hs1) (le_csInf ⟨s, hs1⟩ fun t ht ↦ ?_)
    by_contra! hts
    exact ht (layerIdeal_antitone O r (Nat.succ_le_of_lt hts) hs)

end LocalRing

section DiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}

/-- The normalized derivative `h_P = ϖ⁻ˢ P' ∈ κ((T))` of `P ∈ (O ⧸ 𝔪 ^ (r + 1))((T))`, where
`s = s(P)` is the derivative level of `P`: the layer of `P'` in `Λ_s ⧸ Λ_{s + 1} ≃ κ((T))`
(Yuan, Definition 2.5). -/
def normalizedDerivative (P : LaurentSeries (Truncation O r)) : LaurentSeries (ResidueField O) :=
  layer (derivativeLevel P) (derivative (Truncation O r) P)

/-- `h_P ≠ 0` if `P' ≠ 0`. -/
theorem normalizedDerivative_ne_zero {P : LaurentSeries (Truncation O r)}
    (h : derivative (Truncation O r) P ≠ 0) : normalizedDerivative P ≠ 0 :=
  (layer_ne_zero_iff (derivative_mem_layerIdeal_derivativeLevel P)).mpr
    (derivative_notMem_layerIdeal_derivativeLevel_add_one h)

private theorem derivative_conj_mem_layerIdeal_iff {P : LaurentSeries (Truncation O r)}
    (hP : IsAdmissible P) {H : PowerSeries (Truncation O r)} (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) (j : ℕ) :
    derivative (Truncation O r) (conj H P) ∈ layerIdeal O r j ↔
      derivative (Truncation O r) P ∈ layerIdeal O r j := by
  have hDH := isUnit_derivative_ofPowerSeries H hl
  have hchain : substEquiv H (derivative (Truncation O r) (conj H P)) *
      derivative (Truncation O r) (HahnSeries.ofPowerSeries ℤ _ H) =
      subst P (derivative (Truncation O r) (HahnSeries.ofPowerSeries ℤ _ H)) *
        derivative (Truncation O r) P := by
    rw [substEquiv_apply hH hl, ← derivative_subst (isAdmissible_ofPowerSeries hH hl),
      subst_ofPowerSeries_conj hH hl, derivative_subst hP]
  rw [← algEquiv_mem_layerIdeal_iff O (substEquiv H), ← Ideal.mul_unit_mem_iff_mem _ hDH, hchain,
    Ideal.unit_mul_mem_iff_mem _ (hDH.map (subst P))]

/-- Yuan, Lemma 2.4 (2): for a power series `H` with `H(0) = 0` and `H'(0)` a unit, conjugation by
`H` preserves the derivative level, `s(H ∘ P ∘ H^{∘-1}) = s(P)`. -/
theorem derivativeLevel_conj {P : LaurentSeries (Truncation O r)} (hP : IsAdmissible P)
    {H : PowerSeries (Truncation O r)} (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    derivativeLevel (conj H P) = derivativeLevel P := by
  simp only [derivativeLevel, derivative_conj_mem_layerIdeal_iff hP hH hl]

private theorem layer_subst (G : LaurentSeries (Truncation O r)) {j : ℕ}
    {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    layer j (subst G X) = subst (mapRingHom (residue O r) G) (layer j X) :=
  layer_algHom _ _ (mapRingHom_subst (residue O r) G) hX

variable (p : ℕ)

private theorem coeff_derivative_natCast_mul_sub_one {R : Type*} [CommRing R]
    (P : LaurentSeries R) (ℓ : ℤ) :
    (derivative R P).coeff ((p : ℤ) * ℓ - 1) = (p : R) * ((ℓ : R) * P.coeff ((p : ℤ) * ℓ)) := by
  rw [coeff_derivative, sub_add_cancel, Int.cast_mul, Int.cast_natCast, mul_assoc]

private theorem natCast_mem_maximalIdeal_pow {k : ℕ} (hk : k ≤ absoluteRamificationIdx p O)
    (hkr : k ≤ r + 1) : (p : Truncation O r) ∈ maximalIdeal (Truncation O r) ^ k := by
  rw [← map_natCast (mk O r), mk_mem_maximalIdeal_pow_iff O hkr]
  exact Ideal.pow_le_pow_right hk (natCast_mem_maximalIdeal_pow_absoluteRamificationIdx p)

/-- Yuan, Lemma 2.4: if `p ≠ 0` in `O` and `P ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` reduces to `T ^ p`,
then `P' ≠ 0`. -/
theorem derivative_ne_zero [NeZero (p : O)]
    {P : LaurentSeries (Truncation O (absoluteRamificationIdx p O))}
    (hP : mapRingHom (residue O (absoluteRamificationIdx p O)) P = HahnSeries.single (p : ℤ) 1) :
    derivative (Truncation O (absoluteRamificationIdx p O)) P ≠ 0 := by
  have hunit : IsUnit (P.coeff p) := by
    rw [isUnit_iff_residue_ne_zero, ← mapRingHom_coeff, hP, HahnSeries.coeff_single_same]
    exact one_ne_zero
  have hpe : (p : Truncation O (absoluteRamificationIdx p O)) ≠ 0 := by
    rw [← map_natCast (mk O _), ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_notMem_maximalIdeal_pow_absoluteRamificationIdx_add_one p
  intro h
  have hc := coeff_derivative_natCast_mul_sub_one p P 1
  rw [h, HahnSeries.coeff_zero, mul_one, Int.cast_one, one_mul] at hc
  exact hpe (hunit.mul_left_eq_zero.mp hc.symm)

private theorem coeff_normalizedDerivative_of_eq {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel P = absoluteRamificationIdx p O) (ℓ : ℤ) :
    (normalizedDerivative P).coeff ((p : ℤ) * ℓ - 1) =
      (layer (absoluteRamificationIdx p O) (HahnSeries.C (p : Truncation O r))).coeff 0 *
        ((ℓ : ResidueField O) *
          (HahnSeries.single (p : ℤ) (1 : ResidueField O)).coeff ((p : ℤ) * ℓ)) := by
  have hDP := derivative_mem_layerIdeal_derivativeLevel P
  rw [hs] at hDP
  have hpe := natCast_mem_maximalIdeal_pow (r := r) p le_rfl
    (hs ▸ (derivativeLevel_le P).trans r.le_succ)
  rw [normalizedDerivative, hs, coeff_layer_eq_of_coeff_eq_mul hDP hpe
    (coeff_derivative_natCast_mul_sub_one p P ℓ), map_mul, map_intCast, ← hP, mapRingHom_coeff]

private theorem coeff_layer_C_natCast_ne_zero [NeZero (p : O)]
    (her : absoluteRamificationIdx p O ≤ r) :
    (layer (absoluteRamificationIdx p O) (HahnSeries.C (p : Truncation O r))).coeff 0 ≠ 0 := by
  rw [ne_eq, coeff_layer_eq_zero_iff (C_mem_layerIdeal O
      (natCast_mem_maximalIdeal_pow p le_rfl (her.trans r.le_succ))),
    HahnSeries.C_apply, HahnSeries.coeff_single_same, ← map_natCast (mk O r),
    mk_mem_maximalIdeal_pow_iff O (Nat.succ_le_succ her)]
  exact natCast_notMem_maximalIdeal_pow_absoluteRamificationIdx_add_one p

variable [Fact p.Prime]

/-- A Laurent series reducing to `T ^ p` is admissible. -/
theorem isAdmissible_of_mapRingHom_residue_eq {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1) : IsAdmissible P :=
  (isAdmissible_mapRingHom_iff (residue O r) P).mp
    (hP ▸ isAdmissible_single (by exact_mod_cast (Fact.out : p.Prime).pos) isUnit_one)

variable [Fact (Nat.card (ResidueField O) = p)]

private theorem charP_residueField : CharP (ResidueField O) p :=
  charP_of_natCard_eq_prime Fact.out

private theorem subst_single_eq_pow (f : LaurentSeries (ResidueField O)) :
    subst (HahnSeries.single (p : ℤ) 1) f = f ^ p := by
  have hκ : Nat.card (ResidueField O) = p := Fact.out
  have : Finite (ResidueField O) :=
    Nat.finite_of_card_ne_zero (hκ ▸ (Fact.out : p.Prime).ne_zero)
  simpa only [hκ] using subst_single_natCard_eq_pow f

/-- Yuan, Lemma 2.4 (1), equation (2.2): let `P` reduce to `T ^ p` and let `G` commute with `P`,
`G ∘ P = P ∘ G`, where the reduction `f` of `G` lies in `T κ⟦T⟧` and has nonzero linear
coefficient. Then `h_P ∘ f = (f')^(p - 1) h_P`. -/
theorem subst_normalizedDerivative_of_commute {P G : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1) (hG : IsAdmissible G)
    (hG1 : (mapRingHom (residue O r) G).coeff 1 ≠ 0) (hcomm : subst P G = subst G P) :
    subst (mapRingHom (residue O r) G) (normalizedDerivative P) =
      derivative (ResidueField O) (mapRingHom (residue O r) G) ^ (p - 1) *
        normalizedDerivative P := by
  have hD : derivative (ResidueField O) (mapRingHom (residue O r) G) ≠ 0 :=
    HahnSeries.ne_zero_of_coeff_ne_zero (g := 0) (by
      rwa [coeff_derivative, zero_add, Int.cast_one, one_mul])
  have hDP := derivative_mem_layerIdeal_derivativeLevel P
  have hchain : derivative (Truncation O r) P * subst P (derivative (Truncation O r) G) =
      subst G (derivative (Truncation O r) P) * derivative (Truncation O r) G := by
    rw [mul_comm, ← derivative_subst (isAdmissible_of_mapRingHom_residue_eq p hP), hcomm,
      derivative_subst hG]
  have h := congrArg (layer (derivativeLevel P)) hchain
  rw [layer_mul hDP, layer_mul (algHom_mem_layerIdeal O (subst G) hDP),
    layer_subst G hDP, mapRingHom_subst, hP, subst_single_eq_pow, mapRingHom_derivative] at h
  rw [normalizedDerivative]
  apply mul_right_cancel₀ hD
  rw [← h, ← pow_sub_one_mul (Fact.out : p.Prime).ne_zero]
  ring

/-- Yuan, Lemma 2.4 (2): if `P` reduces to `T ^ p` and `H` is a power series with `H(0) = 0` and
`H'(0)` a unit, then `H ∘ P ∘ H^{∘-1}` reduces to `T ^ p`. -/
theorem mapRingHom_residue_conj {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    {H : PowerSeries (Truncation O r)} (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    mapRingHom (residue O r) (conj H P) = HahnSeries.single (p : ℤ) 1 := by
  have hH' := constantCoeff_map_eq_zero (residue O r) hH
  have hl' := isUnit_coeff_one_map (residue O r) hl
  have hX : (HahnSeries.single (p : ℤ) 1 : LaurentSeries (ResidueField O)) =
      HahnSeries.single 1 1 ^ p := by
    rw [HahnSeries.single_pow, one_pow, nsmul_one]
  rw [mapRingHom_conj _ hH hl, hP, conj_eq_iff_subst hH' hl', subst_single_eq_pow, hX, map_pow,
    subst_X (isAdmissible_ofPowerSeries hH' hl')]

/-- Yuan, Lemma 2.4 (2), equation (2.3): if `P` reduces to `T ^ p` and `H` is a power series with
`H(0) = 0` and `H'(0)` a unit and reduction `H̄`, then `P_H = H ∘ P ∘ H^{∘-1}` satisfies
`h_{P_H} ∘ H̄ = (H̄')^(p - 1) h_P`. -/
theorem subst_normalizedDerivative_conj {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    {H : PowerSeries (Truncation O r)} (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    subst (HahnSeries.ofPowerSeries ℤ _ (H.map (residue O r))) (normalizedDerivative (conj H P)) =
      derivative (ResidueField O) (HahnSeries.ofPowerSeries ℤ _ (H.map (residue O r))) ^ (p - 1) *
        normalizedDerivative P := by
  have hPadm := isAdmissible_of_mapRingHom_residue_eq p hP
  have hDP := derivative_mem_layerIdeal_derivativeLevel P
  have hDPH := (derivative_conj_mem_layerIdeal_iff hPadm hH hl _).mpr hDP
  have hD : derivative (ResidueField O)
      (HahnSeries.ofPowerSeries ℤ _ (H.map (residue O r))) ≠ 0 :=
    (isUnit_derivative_ofPowerSeries _ (isUnit_coeff_one_map _ hl)).ne_zero
  have hchain : subst (HahnSeries.ofPowerSeries ℤ _ H) (derivative (Truncation O r) (conj H P)) *
      derivative (Truncation O r) (HahnSeries.ofPowerSeries ℤ _ H) =
      derivative (Truncation O r) P *
        subst P (derivative (Truncation O r) (HahnSeries.ofPowerSeries ℤ _ H)) := by
    rw [← derivative_subst (isAdmissible_ofPowerSeries hH hl), subst_ofPowerSeries_conj hH hl,
      derivative_subst hPadm, mul_comm]
  have h := congrArg (layer (derivativeLevel P)) hchain
  rw [layer_mul (algHom_mem_layerIdeal O _ hDPH), layer_subst _ hDPH, layer_mul hDP,
    mapRingHom_subst, hP, subst_single_eq_pow, mapRingHom_derivative,
    mapRingHom_ofPowerSeries] at h
  rw [normalizedDerivative, normalizedDerivative, derivativeLevel_conj hPadm hH hl]
  apply mul_right_cancel₀ hD
  rw [h, ← pow_sub_one_mul (Fact.out : p.Prime).ne_zero]
  ring

/-- Yuan, Lemma 2.4 (2): if `P` reduces to `T ^ p` and `H` is a power series with `H(0) = 0` and
`H'(0)` a unit, then `v_T(h_{H ∘ P ∘ H^{∘-1}}) = v_T(h_P)`. -/
theorem order_normalizedDerivative_conj {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    {H : PowerSeries (Truncation O r)} (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    (normalizedDerivative (conj H P)).order = (normalizedDerivative P).order := by
  have hH' := constantCoeff_map_eq_zero (residue O r) hH
  have hl' := isUnit_coeff_one_map (residue O r) hl
  have h := subst_normalizedDerivative_conj p hP hH hl
  rw [← substEquiv_apply hH' hl'] at h
  by_cases h0 : normalizedDerivative P = 0
  · rw [h0, mul_zero, map_eq_zero_iff _ (substEquiv _).injective] at h
    rw [h, h0]
  · rw [← order_substEquiv hH' hl', h,
      HahnSeries.order_mul (pow_ne_zero _ (isUnit_derivative_ofPowerSeries _ hl').ne_zero) h0,
      HahnSeries.order_pow, order_derivative_ofPowerSeries hl', smul_zero, zero_add]

/-- Yuan, Lemma 2.4 (3): if `s(P) < e`, then `h_P = A'` for some `A ∈ κ((T))`. -/
theorem exists_normalizedDerivative_eq_derivative {P : LaurentSeries (Truncation O r)}
    (hs : derivativeLevel P < absoluteRamificationIdx p O) :
    ∃ A : LaurentSeries (ResidueField O),
      normalizedDerivative P = derivative (ResidueField O) A := by
  have := charP_residueField p (O := O)
  obtain ⟨A, hA⟩ := (exists_derivative_iff p (normalizedDerivative P)).mpr fun ℓ ↦ by
    rw [normalizedDerivative, coeff_layer_eq_zero_iff (derivative_mem_layerIdeal_derivativeLevel P),
      coeff_derivative_natCast_mul_sub_one]
    exact Ideal.mul_mem_right _ _ (natCast_mem_maximalIdeal_pow p hs
      (Nat.succ_le_succ (derivativeLevel_le P)))
  exact ⟨A, hA.symm⟩

/-- Yuan, Lemma 2.4 (3): if `p ≠ 0` in `O`, `P` reduces to `T ^ p` and `s(P) = e`, then
`h_P = c T^(p - 1) + A'` for some `c ≠ 0` in `κ` and `A ∈ κ((T))`. -/
theorem exists_normalizedDerivative_eq_single_add_derivative [NeZero (p : O)]
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel P = absoluteRamificationIdx p O) :
    ∃ c : ResidueField O, c ≠ 0 ∧ ∃ A : LaurentSeries (ResidueField O),
      normalizedDerivative P =
        HahnSeries.single ((p : ℤ) - 1) c + derivative (ResidueField O) A := by
  refine ⟨_, coeff_layer_C_natCast_ne_zero p (hs ▸ derivativeLevel_le P), ?_⟩
  have := charP_residueField p (O := O)
  obtain ⟨A, hA⟩ := (exists_derivative_iff p (normalizedDerivative P -
      HahnSeries.single ((p : ℤ) - 1)
        ((layer (absoluteRamificationIdx p O) (HahnSeries.C (p : Truncation O r))).coeff 0))).mpr
    fun ℓ ↦ by
      rw [HahnSeries.coeff_sub, coeff_normalizedDerivative_of_eq p hP hs]
      by_cases hℓ : ℓ = 1
      · subst hℓ
        simp
      · have hpℓ : (p : ℤ) * ℓ ≠ p := fun h ↦ hℓ (mul_left_cancel₀
          (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (h.trans (mul_one _).symm))
        rw [HahnSeries.coeff_single_of_ne hpℓ, HahnSeries.coeff_single_of_ne (by omega),
          mul_zero, mul_zero, sub_zero]
  exact ⟨A, by rw [hA, add_sub_cancel]⟩

private theorem coeff_derivative_normalizedDerivative_ne_zero [NeZero (p : O)]
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel P = absoluteRamificationIdx p O) :
    (derivative (ResidueField O) (normalizedDerivative P)).coeff ((p : ℤ) - 2) ≠ 0 := by
  have := charP_residueField p (O := O)
  have h := coeff_normalizedDerivative_of_eq p hP hs 1
  simp only [mul_one, Int.cast_one, HahnSeries.coeff_single_same] at h
  rw [coeff_derivative, show (p : ℤ) - 2 + 1 = p - 1 by ring, h, Int.cast_sub, Int.cast_natCast,
    CharP.cast_eq_zero, Int.cast_one, zero_sub, neg_one_mul, neg_ne_zero]
  exact coeff_layer_C_natCast_ne_zero p (hs ▸ derivativeLevel_le P)

/-- Yuan, Lemma 2.4 (3): if `p ≠ 0` in `O`, `P` reduces to `T ^ p` and `s(P) = e`, then
`h_P' ≠ 0`. -/
theorem derivative_normalizedDerivative_ne_zero [NeZero (p : O)]
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel P = absoluteRamificationIdx p O) :
    derivative (ResidueField O) (normalizedDerivative P) ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (coeff_derivative_normalizedDerivative_ne_zero p hP hs)

/-- Yuan, Lemma 2.4 (3): if `p ≠ 0` in `O`, `P` reduces to `T ^ p` and `s(P) = e`, then
`v_T(h_P') ≤ p - 2`. -/
theorem order_derivative_normalizedDerivative_le [NeZero (p : O)]
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hs : derivativeLevel P = absoluteRamificationIdx p O) :
    (derivative (ResidueField O) (normalizedDerivative P)).order ≤ (p : ℤ) - 2 :=
  HahnSeries.order_le_of_coeff_ne_zero (coeff_derivative_normalizedDerivative_ne_zero p hP hs)

/-- Yuan, Lemma 2.4: if `p ≠ 0` in `O` and `P ∈ (O ⧸ 𝔪 ^ (e + 1))((T))` reduces to `T ^ p`, then
`1 ≤ s(P)`. -/
theorem one_le_derivativeLevel [NeZero (p : O)]
    {P : LaurentSeries (Truncation O (absoluteRamificationIdx p O))}
    (hP : mapRingHom (residue O (absoluteRamificationIdx p O)) P = HahnSeries.single (p : ℤ) 1) :
    1 ≤ derivativeLevel P := by
  have := charP_residueField p (O := O)
  by_contra! h
  have h1 := derivative_notMem_layerIdeal_derivativeLevel_add_one (derivative_ne_zero p hP)
  rw [Nat.lt_one_iff.mp h] at h1
  exact h1 (derivative_mem_layerIdeal_one O p hP)

end DiscreteValuationRing

end Truncation

end FalseTateNonliftability

end NormalizedDerivative

/-! ### The valuation bound at derivative level `e` -/

section ValuationBound

open IsLocalRing (ResidueField)

namespace LaurentSeries

section CommRing

variable {R : Type*} [CommRing R]

private theorem sub_X_mem_of_normalForm {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d) {α : R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1) :=
  mem_orderAddSubgroup_of_sub_single_mem (orderAddSubgroup_antitone (by omega) hg)

private theorem derivative_sub_one_mem_of_normalForm (p : ℕ) [CharP R p] {g : LaurentSeries R}
    {d : ℤ} (hdiv : (p : ℤ) ∣ d + 1) {α : R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1)) :
    derivative R g - 1 ∈ orderAddSubgroup (2 * d) := by
  have hcast : ((d + 1 : ℤ) : R) = 0 := by
    obtain ⟨n, hn⟩ := hdiv
    rw [hn, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero R p, zero_mul]
  simpa [hcast] using derivative_mem_orderAddSubgroup _ _ hg

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Let `k` have characteristic `p`, let `g = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ≠ 0`,
`d ≥ 1` and `d ≡ -1 (mod p)`, and let `h ∈ k((T))` satisfy `h ∘ g = (g')^(p - 1) h`, `h' ≠ 0` and
`v_T(h') ≤ p - 2`. Then `v_T(h) ≤ p - 1 - d` (Yuan, proof of Theorem 3.1). -/
theorem order_le_of_subst_eq_derivative_pow_mul (p : ℕ) [CharP k p] {g : LaurentSeries k}
    {d : ℤ} (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1) {α : k} (hα : α ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (2 * d + 1))
    {h : LaurentSeries k} (hD : derivative k h ≠ 0)
    (hDorder : (derivative k h).order ≤ (p : ℤ) - 2)
    (hchain : subst g h = derivative k g ^ (p - 1) * h) :
    h.order ≤ (p : ℤ) - 1 - d := by
  have hX := sub_X_mem_of_normalForm hd hg
  have hXorder : (g - HahnSeries.single (1 : ℤ) 1).order = d + 1 :=
    order_eq_of_sub_single_mem hα (orderAddSubgroup_antitone (by omega) hg)
  have hXne : g - HahnSeries.single (1 : ℤ) 1 ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.order_zero] at hXorder
    omega
  have hdiff : subst g h - h ∈ orderAddSubgroup (h.order + 2 * d) := by
    rw [hchain, show derivative k g ^ (p - 1) * h - h = (derivative k g ^ (p - 1) - 1) * h by
      ring, add_comm]
    exact mul_mem_orderAddSubgroup (pow_sub_one_mem_orderAddSubgroup (by omega)
      (derivative_sub_one_mem_of_normalForm p hdiv hg) _) (mem_orderAddSubgroup_order h)
  have hprod : (g - HahnSeries.single (1 : ℤ) 1) * derivative k h ∈
      orderAddSubgroup (h.order + 2 * d) := by
    simpa only [sub_sub_cancel] using
      sub_mem hdiff (subst_taylor_mem_orderAddSubgroup hd hX (mem_orderAddSubgroup_order h))
  rw [mem_orderAddSubgroup, ← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hXne hD),
    WithTop.coe_le_coe, HahnSeries.order_mul hXne hD, hXorder] at hprod
  omega

end Field

end LaurentSeries

namespace FalseTateNonliftability.Truncation

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
  (p : ℕ) [Fact p.Prime] [Fact (Nat.card (ResidueField O) = p)] [NeZero (p : O)]

/-- **Theorem 3.1** (Yuan), valuation bound at level `e`. Let `p ≠ 0` in `O`, let `κ = 𝔽_p` and
`e = v(p)`. Let `P, G ∈ (O ⧸ 𝔪 ^ (r + 1))((T))`, where `P` reduces to `T ^ p`,
`G ∘ P = P ∘ G` and `s(P) = e`, and let the reduction `f` of `G` satisfy
`f = T + α T ^ (d + 1) + O(T ^ (2 d + 1))` with `α ≠ 0`, `d ≥ 1` and `d ≡ -1 (mod p)`. Then
`v_T(h_P) ≤ p - 1 - d`. -/
theorem order_normalizedDerivative_le {P G : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1)
    (hcomm : subst P G = subst G P) (hs : derivativeLevel P = absoluteRamificationIdx p O)
    {d : ℤ} (hd : 1 ≤ d) (hdiv : (p : ℤ) ∣ d + 1) {α : ResidueField O} (hα : α ≠ 0)
    (hG : mapRingHom (residue O r) G - HahnSeries.single (1 : ℤ) 1 -
      HahnSeries.single (d + 1) α ∈ orderAddSubgroup (2 * d + 1)) :
    (normalizedDerivative P).order ≤ (p : ℤ) - 1 - d := by
  have := charP_of_natCard_eq_prime (Fact.out : Nat.card (ResidueField O) = p)
  have hX := sub_X_mem_of_normalForm hd hG
  have hadm : IsAdmissible G := (isAdmissible_mapRingHom_iff (residue O r) G).mp
    (isAdmissible_of_sub_X_mem (orderAddSubgroup_antitone (by omega) hX))
  have h1 : (mapRingHom (residue O r) G).coeff 1 ≠ 0 := by
    have hc := (mem_orderAddSubgroup_iff_coeff _ _).mp hX 1 (by omega)
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
    rw [hc]
    exact one_ne_zero
  exact order_le_of_subst_eq_derivative_pow_mul p hd hdiv hα hG
    (derivative_normalizedDerivative_ne_zero p hP hs)
    (order_derivative_normalizedDerivative_le p hP hs)
    (subst_normalizedDerivative_of_commute p hP hadm h1 hcomm)

end FalseTateNonliftability.Truncation

end ValuationBound
