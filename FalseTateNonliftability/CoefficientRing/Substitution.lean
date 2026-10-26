/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition

/-!
# Substitution and coordinate changes in the coefficient ring `A`

Let `O` be a local principal ideal ring with maximal ideal `𝔪` and residue field `κ` (in Yuan, the
ring of integers of a finite extension `F` of `ℚ_p`), and let `A` be the `𝔪`-adic completion of
`O((T))` (`FalseTateNonliftability.CoefficientRing O`, Yuan, Definition 1.1). For Laurent series
`Q` and `G`, write `Q ∘ G = Q(G)` for the substitution of `G` for the variable. An element `G ∈ A`
is admissible if its reduction $\bar{G} \in \kappa((T))$ is nonzero with $v_T(\bar{G}) \ge 1$. Yuan,
Lemma 2.1 over `A`: for admissible `G`, the substitutions `Q ↦ Q(G)` on the rings
`(O ⧸ 𝔪 ^ (r + 1))((T))`
(`LaurentSeries.subst`) are compatible, and their inverse limit is the unique `O`-algebra
endomorphism `Q ↦ Q(G)` of `A` sending `T` to `G` that is `T`-adically continuous modulo every
`𝔪 ^ (r + 1)`; moreover `(Q ∘ G) ∘ H = Q ∘ (G ∘ H)`.

Let `H` be a power series with `H(0) = 0` and invertible linear coefficient, and let `H^{∘-1}` be
its compositional inverse (Yuan, Lemma 2.1 (3)). The conjugate of a Laurent series `P` by `H` is
`H ∘ P ∘ H^{∘-1}`, both over a local Artinian principal ideal ring and over `A`. Conjugation by `H`
preserves admissibility and composition, hence commutation, it is inverted by conjugation by
`H^{∘-1}`, it commutes with reduction of coefficients, and on power series over `κ` it is
`PowerSeries.conj`. Every such power series over `κ` is the reduction of one over `O`. These are
the ingredients of Yuan, Proposition 2.3: if `π' = ev_π(V)` is another uniformizer of the field of
norms and `H` lifts `V`, conjugation by `H` transports lifts with respect to `π` to lifts with
respect to `π'`, in `A` and modulo every power of `𝔪`.

## Main definitions

* `FalseTateNonliftability.CoefficientRing.X`: the variable `T` of `A`.
* `FalseTateNonliftability.CoefficientRing.IsAdmissible G`: the reduction of `G` to `κ((T))` is
  nonzero with positive valuation.
* `FalseTateNonliftability.CoefficientRing.subst G`: the substitution `Q ↦ Q(G)` in `A`.
* `LaurentSeries.conj H P`: the conjugate `H ∘ P ∘ H^{∘-1}` of a Laurent series `P`.
* `FalseTateNonliftability.CoefficientRing.conj H P`: the conjugate `H ∘ P ∘ H^{∘-1}` of `P ∈ A`.

## Main results

* `FalseTateNonliftability.CoefficientRing.reduction_subst`,
  `FalseTateNonliftability.CoefficientRing.residue_subst`: substitution commutes with reduction
  modulo `𝔪 ^ (r + 1)` and with reduction to `κ((T))`.
* `FalseTateNonliftability.CoefficientRing.subst_X`: `T(G) = G` (Yuan, Lemma 2.1 (1), over `A`).
* `FalseTateNonliftability.CoefficientRing.subst_unique`: uniqueness of substitution (Yuan,
  Lemma 2.1 (1), over `A`).
* `FalseTateNonliftability.CoefficientRing.subst_comp_subst`: `(Q ∘ G) ∘ H = Q ∘ (G ∘ H)` (Yuan,
  Lemma 2.1 (2), over `A`).
* `LaurentSeries.conj_eq_iff_subst`: `H ∘ P ∘ H^{∘-1} = Q` if and only if `H ∘ P = Q ∘ H`.
* `LaurentSeries.conj_subst`, `LaurentSeries.conj_commute_iff`: conjugation preserves composition,
  and preserves and reflects commutation of admissible series.
* `LaurentSeries.mapRingHom_conj`, `LaurentSeries.conj_ofPowerSeries`: conjugation commutes with
  coefficient maps and is `PowerSeries.conj` on power series.
* `FalseTateNonliftability.CoefficientRing.reduction_conj`,
  `FalseTateNonliftability.CoefficientRing.residue_conj`: conjugation in `A` reduces to
  conjugation over `O ⧸ 𝔪 ^ (r + 1)` and over `κ`.
* `FalseTateNonliftability.CoefficientRing.conj_subst`,
  `FalseTateNonliftability.CoefficientRing.conj_commute_iff`: the same laws in `A`.
* `FalseTateNonliftability.CoefficientRing.exists_map_residue_eq`,
  `FalseTateNonliftability.Truncation.exists_map_residue_eq`: coordinate changes over `κ` lift to
  `O` and to `O ⧸ 𝔪 ^ (r + 1)` (Yuan, proof of Proposition 2.3).

## Implementation notes

`CoefficientRing.subst G` is defined for every `G ∈ A` and is the identity if `G` is not
admissible, and `conj H P` is defined for every power series `H`; their lemmas assume that `G` is
admissible and that `H(0) = 0` and `H'(0)` is a unit. The Laurent series part of the file is stated
over local Artinian principal ideal rings, the coefficient rings of `LaurentSeries.subst`, which
include `κ` and the truncations `O ⧸ 𝔪 ^ (r + 1)` of a discrete valuation ring `O`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.1 and Proposition 2.3.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/

public section

noncomputable section

/-! ### Substitution in `A` -/

section Subst

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries
open scoped LaurentSeries.OrderTopology

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The variable `T` of `A`. -/
@[expose] def X : CoefficientRing O :=
  algebraMap (LaurentSeries O) (CoefficientRing O) (HahnSeries.single 1 1)

/-- The reduction of `T ∈ A` modulo `𝔪 ^ (r + 1)` is `T`. -/
@[simp]
theorem reduction_X (r : ℕ) : reduction O r X = HahnSeries.single 1 1 := by
  rw [X, reduction_algebraMap_laurentSeries, mapRingHom_single, map_one]

/-- The image of `P ∈ O⟦T⟧` in `κ((T))` is the coefficientwise reduction of `P`. -/
@[simp]
theorem residue_algebraMap_powerSeries (P : PowerSeries O) :
    residue O (algebraMap (PowerSeries O) (CoefficientRing O) P) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (IsLocalRing.residue O) P) := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries O) (LaurentSeries O),
    residue_algebraMap_laurentSeries, coe_algebraMap, mapRingHom_ofPowerSeries]

/-- An element `G` of `A` is admissible if its reduction $\bar{G} \in \kappa((T))$ is nonzero with
$v_T(\bar{G}) \ge 1$. -/
@[expose] def IsAdmissible (G : CoefficientRing O) : Prop :=
  LaurentSeries.IsAdmissible (residue O G)

/-- `G ∈ A` is admissible if and only if its reduction to `κ((T))` is admissible. -/
theorem isAdmissible_iff_isAdmissible_residue (G : CoefficientRing O) :
    IsAdmissible G ↔ LaurentSeries.IsAdmissible (residue O G) :=
  Iff.rfl

variable [IsPrincipalIdealRing O]

/-- An element of `A` is admissible if and only if its reduction modulo `𝔪 ^ (r + 1)` is. -/
theorem isAdmissible_iff_reduction (r : ℕ) (G : CoefficientRing O) :
    IsAdmissible G ↔ LaurentSeries.IsAdmissible (reduction O r G) := by
  rw [isAdmissible_iff_isAdmissible_residue, ← mapRingHom_residue_reduction O r,
    isAdmissible_mapRingHom_iff]

private theorem mapRingHom_factor_subst_reduction (G : CoefficientRing O) {s r : ℕ}
    (hsr : s ≤ r) (f : CoefficientRing O) :
    mapRingHom (Truncation.factor O hsr)
        (LaurentSeries.subst (reduction O r G) (reduction O r f)) =
      LaurentSeries.subst (reduction O s G) (reduction O s f) := by
  rw [mapRingHom_subst, mapRingHom_factor_reduction, mapRingHom_factor_reduction]

private theorem mapRingHom_factor_comp_subst_reduction (G : CoefficientRing O) {s r : ℕ}
    (hsr : s ≤ r) :
    (mapRingHom (Truncation.factor O hsr)).comp
        ((LaurentSeries.subst (reduction O r G)).toRingHom.comp (reduction O r)) =
      (LaurentSeries.subst (reduction O s G)).toRingHom.comp (reduction O s) :=
  RingHom.ext (mapRingHom_factor_subst_reduction G hsr)

private def substRingHom (G : CoefficientRing O) : CoefficientRing O →+* CoefficientRing O :=
  lift (fun r ↦ (LaurentSeries.subst (reduction O r G)).toRingHom.comp (reduction O r))
    fun hsr ↦ mapRingHom_factor_comp_subst_reduction G hsr

private theorem reduction_substRingHom (G : CoefficientRing O) (r : ℕ) (f : CoefficientRing O) :
    reduction O r (substRingHom G f) = LaurentSeries.subst (reduction O r G) (reduction O r f) :=
  reduction_lift _ (fun hsr ↦ mapRingHom_factor_comp_subst_reduction G hsr) r f

private theorem substRingHom_algebraMap (G : CoefficientRing O) (b : O) :
    substRingHom G (algebraMap O (CoefficientRing O) b) = algebraMap O (CoefficientRing O) b :=
  ext_reduction O fun r ↦ by rw [reduction_substRingHom, reduction_algebraMap, subst_C]

/-- Substitution `f ↦ f(G)` of `G ∈ A` for the variable: the `O`-algebra endomorphism of `A`
that reduces modulo every `𝔪 ^ (r + 1)` to substitution of the reduction of `G`
(`reduction_subst`). It is the identity if `G` is not admissible. -/
@[pp_nodot]
def subst (G : CoefficientRing O) : CoefficientRing O →ₐ[O] CoefficientRing O :=
  { substRingHom G with commutes' := substRingHom_algebraMap G }

/-- Substitution commutes with reduction modulo `𝔪 ^ (r + 1)`. -/
@[simp]
theorem reduction_subst (G : CoefficientRing O) (r : ℕ) (f : CoefficientRing O) :
    reduction O r (subst G f) = LaurentSeries.subst (reduction O r G) (reduction O r f) :=
  reduction_substRingHom G r f

/-- Substitution commutes with reduction to `κ((T))`. -/
@[simp]
theorem residue_subst (G f : CoefficientRing O) :
    residue O (subst G f) = LaurentSeries.subst (residue O G) (residue O f) := by
  rw [← mapRingHom_residue_reduction O 0, reduction_subst,
    mapRingHom_subst (Truncation.residue O 0)]
  simp only [mapRingHom_residue_reduction]

/-- Substitution of `G` sends `T` to `G` (Yuan, Lemma 2.1 (1), over `A`). -/
@[simp]
theorem subst_X {G : CoefficientRing O} (hG : IsAdmissible G) : subst G X = G :=
  ext_reduction O fun r ↦ by
    rw [reduction_subst, reduction_X,
      LaurentSeries.subst_X ((isAdmissible_iff_reduction r G).mp hG)]

/-- For admissible `G`, `subst G` is the only `O`-algebra endomorphism of `A` sending `T` to `G`
that induces, modulo every `𝔪 ^ (r + 1)`, an endomorphism of `(O ⧸ 𝔪 ^ (r + 1))((T))` continuous
for the `T`-adic topology (Yuan, Lemma 2.1 (1), over `A`). -/
theorem subst_unique {G : CoefficientRing O} (hG : IsAdmissible G)
    (F : CoefficientRing O →ₐ[O] CoefficientRing O)
    (Φ : (r : ℕ) →
      LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (hΦ : ∀ r, Continuous (Φ r))
    (hF : ∀ r f, reduction O r (F f) = Φ r (reduction O r f)) (hX : F X = G) :
    F = subst G := by
  have hΦG (r : ℕ) : Φ r = LaurentSeries.subst (reduction O r G) :=
    LaurentSeries.subst_unique ((isAdmissible_iff_reduction r G).mp hG) (Φ r) (hΦ r)
      (by rw [← reduction_X (O := O) r, ← hF, hX])
  exact AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by rw [hF, hΦG, reduction_subst]

/-- If `G` and `H` are admissible, so is `G(H)`. -/
theorem IsAdmissible.subst {G H : CoefficientRing O} (hG : IsAdmissible G)
    (hH : IsAdmissible H) : IsAdmissible (CoefficientRing.subst H G) := by
  rw [isAdmissible_iff_isAdmissible_residue, residue_subst]
  exact LaurentSeries.IsAdmissible.subst hG hH

/-- Composition of substitutions: `f(G)(H) = f(G(H))` for admissible `G` and `H` (Yuan,
Lemma 2.1 (2), over `A`). -/
theorem subst_comp_subst {G H : CoefficientRing O} (hG : IsAdmissible G) (hH : IsAdmissible H) :
    (subst H).comp (subst G) = subst (subst H G) :=
  AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by
    simp only [AlgHom.comp_apply, reduction_subst]
    exact subst_comp_subst_apply ((isAdmissible_iff_reduction r G).mp hG)
      ((isAdmissible_iff_reduction r H).mp hH) _

end FalseTateNonliftability.CoefficientRing

end Subst

/-! ### Coordinate changes -/

section CoordinateChange

open PowerSeries (constantCoeff_map_eq_zero isUnit_coeff_one_map)

namespace LaurentSeries

open scoped LaurentSeries.OrderTopology

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
  [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsPrincipalIdealRing S]

/-- The conjugate `H ∘ P ∘ H^{∘-1}` of a Laurent series `P` by a power series `H`, where
`H^{∘-1}` is the compositional inverse of `H` (`PowerSeries.compInv`). -/
@[expose] def conj (H : PowerSeries R) (P : LaurentSeries R) : LaurentSeries R :=
  subst (HahnSeries.ofPowerSeries ℤ R H.compInv) (subst P (HahnSeries.ofPowerSeries ℤ R H))

variable {H : PowerSeries R}

private theorem subst_ofPowerSeries_compInv (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) (f : LaurentSeries R) :
    subst (HahnSeries.ofPowerSeries ℤ R H.compInv) f = (substEquiv H).symm f :=
  (substEquiv_symm_apply hH hl f).symm

/-- `H ∘ P ∘ H^{∘-1}` is the image of `H ∘ P` under the inverse of `f ↦ f(H)`. -/
theorem conj_eq_substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) :
    conj H P = (substEquiv H).symm (subst P (HahnSeries.ofPowerSeries ℤ R H)) :=
  subst_ofPowerSeries_compInv hH hl _

/-- `H ∘ P ∘ H^{∘-1} = Q` if and only if `H ∘ P = Q ∘ H`. -/
theorem conj_eq_iff_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P Q : LaurentSeries R} :
    conj H P = Q ↔
      subst P (HahnSeries.ofPowerSeries ℤ R H) = subst (HahnSeries.ofPowerSeries ℤ R H) Q := by
  rw [conj_eq_substEquiv_symm hH hl, AlgEquiv.symm_apply_eq, substEquiv_apply hH hl]

/-- `(H ∘ P ∘ H^{∘-1}) ∘ H = H ∘ P`. -/
theorem subst_ofPowerSeries_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) :
    subst (HahnSeries.ofPowerSeries ℤ R H) (conj H P) =
      subst P (HahnSeries.ofPowerSeries ℤ R H) :=
  ((conj_eq_iff_subst hH hl).mp rfl).symm

/-- Conjugation by `H` preserves admissibility. -/
theorem IsAdmissible.conj {P : LaurentSeries R} (hP : IsAdmissible P)
    (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) : IsAdmissible (LaurentSeries.conj H P) :=
  ((isAdmissible_ofPowerSeries hH hl).subst hP).subst (isAdmissible_ofPowerSeries_compInv H)

/-- Substitution of `H ∘ P ∘ H^{∘-1}` is substitution of `P` conjugated by `f ↦ f(H)`:
`f ∘ (H ∘ P ∘ H^{∘-1}) = ((f ∘ H) ∘ P) ∘ H^{∘-1}`. -/
theorem subst_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (P : LaurentSeries R) :
    subst (conj H P) =
      ((substEquiv H).symm.toAlgHom.comp (subst P)).comp (substEquiv H).toAlgHom := by
  by_cases hP : IsAdmissible P
  · refine (subst_unique (hP.conj hH hl) _ ((continuous_substEquiv_symm H).comp
      ((continuous_subst P).comp (continuous_substEquiv H))) ?_).symm
    change (substEquiv H).symm (subst P (substEquiv H (HahnSeries.single 1 1))) = _
    rw [substEquiv_X hH hl, conj_eq_substEquiv_symm hH hl]
  · rw [conj_eq_substEquiv_symm hH hl, subst_of_not_isAdmissible hP, AlgHom.id_apply,
      ← substEquiv_X hH hl, AlgEquiv.symm_apply_apply, subst_X_left]
    exact AlgHom.ext fun f ↦ ((substEquiv H).symm_apply_apply f).symm

/-- `f ∘ (H ∘ P ∘ H^{∘-1}) = ((f ∘ H) ∘ P) ∘ H^{∘-1}`. -/
theorem subst_conj_apply (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P f : LaurentSeries R) :
    subst (conj H P) f = (substEquiv H).symm (subst P (substEquiv H f)) :=
  AlgHom.congr_fun (subst_conj hH hl P) f

/-- Conjugation preserves composition: `H ∘ (P ∘ G) ∘ H^{∘-1}` is the composite of
`H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`. -/
theorem conj_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {G P : LaurentSeries R}
    (hG : IsAdmissible G) (hP : IsAdmissible P) :
    conj H (subst G P) = subst (conj H G) (conj H P) := by
  rw [subst_conj_apply hH hl, substEquiv_apply hH hl, subst_ofPowerSeries_conj hH hl,
    subst_comp_subst_apply hP hG, conj_eq_substEquiv_symm hH hl]

/-- Conjugating by `H` and then by `H^{∘-1}` is the identity on admissible series. -/
theorem conj_compInv_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : LaurentSeries R} (hP : IsAdmissible P) : conj H.compInv (conj H P) = P := by
  rw [conj_eq_iff_subst (PowerSeries.constantCoeff_compInv H)
      (PowerSeries.isUnit_coeff_one_compInv H), subst_conj_apply hH hl,
    substEquiv_ofPowerSeries hH hl, PowerSeries.subst_compInv_left hH hl,
    HahnSeries.ofPowerSeries_X, subst_X hP, subst_ofPowerSeries_compInv hH hl]

/-- Conjugation by `H` is injective on admissible series. -/
theorem conj_inj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {P G : LaurentSeries R}
    (hP : IsAdmissible P) (hG : IsAdmissible G) : conj H P = conj H G ↔ P = G :=
  ⟨fun h ↦ by rw [← conj_compInv_conj hH hl hP, h, conj_compInv_conj hH hl hG],
    fun h ↦ h ▸ rfl⟩

/-- Conjugation preserves and reflects commutation: `H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`
commute if and only if `P` and `G` commute. -/
theorem conj_commute_iff (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P G : LaurentSeries R} (hP : IsAdmissible P) (hG : IsAdmissible G) :
    subst (conj H P) (conj H G) = subst (conj H G) (conj H P) ↔ subst P G = subst G P := by
  rw [← conj_subst hH hl hP hG, ← conj_subst hH hl hG hP,
    conj_inj hH hl (hG.subst hP) (hP.subst hG)]

/-- Conjugation commutes with coefficient maps: `φ(H ∘ P ∘ H^{∘-1}) = φH ∘ φP ∘ (φH)^{∘-1}`. -/
theorem mapRingHom_conj (φ : R →+* S) (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) : mapRingHom φ (conj H P) = conj (H.map φ) (mapRingHom φ P) := by
  rw [conj, conj, mapRingHom_subst, mapRingHom_subst, mapRingHom_ofPowerSeries,
    mapRingHom_ofPowerSeries, PowerSeries.map_compInv φ hH hl]

/-- On admissible power series `f` with `f(0) = 0`, conjugation is `PowerSeries.conj`. -/
theorem conj_ofPowerSeries {f : PowerSeries R} (hf : f.constantCoeff = 0)
    (hfadm : IsAdmissible (HahnSeries.ofPowerSeries ℤ R f)) (H : PowerSeries R) :
    conj H (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.conj H f) := by
  rw [conj, subst_ofPowerSeries hf hfadm, subst_ofPowerSeries (PowerSeries.constantCoeff_compInv H)
    (isAdmissible_ofPowerSeries_compInv H)]
  rfl

/-- If the image of an admissible `P` under a coefficient map `φ` is a power series `f`, then the
image of `H ∘ P ∘ H^{∘-1}` is `PowerSeries.conj` of `f` by `φ H`. -/
theorem mapRingHom_conj_of_mapRingHom_eq (φ : R →+* S) (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) {P : LaurentSeries R} (hP : IsAdmissible P) {f : PowerSeries S}
    (hf : f.constantCoeff = 0) (hres : mapRingHom φ P = HahnSeries.ofPowerSeries ℤ S f) :
    mapRingHom φ (conj H P) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.conj (H.map φ) f) := by
  rw [mapRingHom_conj φ hH hl, hres, conj_ofPowerSeries hf (hres ▸ hP.map φ)]

end LaurentSeries

namespace FalseTateNonliftability

open LaurentSeries
open IsLocalRing (ResidueField)

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- A power series `w` over `κ` with `w(0) = 0` and `w'(0) ≠ 0` is the coefficientwise reduction of
a power series `H` over `O` with `H(0) = 0` and `H'(0)` a unit. -/
theorem CoefficientRing.exists_map_residue_eq (w : PowerSeries (ResidueField O))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries O, H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (IsLocalRing.residue O) = w := by
  obtain ⟨H, hH⟩ := PowerSeries.map_surjective _ IsLocalRing.residue_surjective w
  have hc : IsLocalRing.residue O H.constantCoeff = 0 := by
    rw [← hw, ← hH, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  have hl : IsUnit (H.coeff 1) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← PowerSeries.coeff_map, hH]
    exact hw'.ne_zero
  refine ⟨H - PowerSeries.C H.constantCoeff, by simp, by simpa using hl, ?_⟩
  rw [map_sub, PowerSeries.map_C, hc, map_zero, sub_zero, hH]

/-- A power series `w` over `κ` with `w(0) = 0` and `w'(0) ≠ 0` is the coefficientwise reduction of
a power series `H` over `O ⧸ 𝔪 ^ (r + 1)` with `H(0) = 0` and `H'(0)` a unit. -/
theorem Truncation.exists_map_residue_eq (r : ℕ) (w : PowerSeries (ResidueField O))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries (Truncation O r), H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (Truncation.residue O r) = w := by
  obtain ⟨H, hH, hl, hres⟩ := CoefficientRing.exists_map_residue_eq w hw hw'
  refine ⟨H.map (Truncation.mk O r), constantCoeff_map_eq_zero _ hH, isUnit_coeff_one_map _ hl,
    ?_⟩
  change PowerSeries.map ((Truncation.residue O r).comp (Truncation.mk O r)) H = w
  rw [Truncation.residue_comp_mk, hres]

namespace CoefficientRing

variable [IsPrincipalIdealRing O]

/-- The conjugate `H ∘ P ∘ H^{∘-1}` of `P ∈ A` by a power series `H` over `O`, where `H^{∘-1}` is
the compositional inverse of `H` (`PowerSeries.compInv`). -/
@[expose] def conj (H : PowerSeries O) (P : CoefficientRing O) : CoefficientRing O :=
  subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv)
    (subst P (algebraMap (PowerSeries O) (CoefficientRing O) H))

variable {H : PowerSeries O}

/-- Conjugation in `A` commutes with reduction modulo `𝔪 ^ (r + 1)`. -/
theorem reduction_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (r : ℕ)
    (P : CoefficientRing O) :
    reduction O r (conj H P) =
      LaurentSeries.conj (H.map (Truncation.mk O r)) (reduction O r P) := by
  rw [conj, reduction_subst, reduction_subst, reduction_algebraMap_powerSeries,
    reduction_algebraMap_powerSeries, PowerSeries.map_compInv _ hH hl]
  rfl

/-- Conjugation in `A` commutes with reduction to `κ((T))`. -/
theorem residue_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : CoefficientRing O) :
    residue O (conj H P) =
      LaurentSeries.conj (H.map (IsLocalRing.residue O)) (residue O P) := by
  rw [conj, residue_subst, residue_subst, residue_algebraMap_powerSeries,
    residue_algebraMap_powerSeries, PowerSeries.map_compInv _ hH hl]
  rfl

/-- If the image of an admissible `P ∈ A` in `κ((T))` is a power series `f`, then the image of
`H ∘ P ∘ H^{∘-1}` is `PowerSeries.conj` of `f` by the reduction of `H`. -/
theorem residue_conj_of_residue_eq (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : CoefficientRing O} (hP : IsAdmissible P) {f : PowerSeries (ResidueField O)}
    (hf : f.constantCoeff = 0) (hres : residue O P = HahnSeries.ofPowerSeries ℤ _ f) :
    residue O (conj H P) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.conj (H.map (IsLocalRing.residue O)) f) := by
  rw [residue_conj hH hl, hres, conj_ofPowerSeries hf
    (hres ▸ (isAdmissible_iff_isAdmissible_residue P).mp hP)]

/-- Conjugation preserves composition: `H ∘ (P ∘ G) ∘ H^{∘-1}` is the composite of
`H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`. -/
theorem conj_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {G P : CoefficientRing O} (hG : IsAdmissible G) (hP : IsAdmissible P) :
    conj H (subst G P) = subst (conj H G) (conj H P) :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj hH hl, reduction_subst, reduction_subst, reduction_conj hH hl,
      reduction_conj hH hl, LaurentSeries.conj_subst (constantCoeff_map_eq_zero _ hH)
        (isUnit_coeff_one_map _ hl) ((isAdmissible_iff_reduction r G).mp hG)
        ((isAdmissible_iff_reduction r P).mp hP)]

/-- Conjugating by `H` and then by `H^{∘-1}` is the identity on admissible elements. -/
theorem conj_compInv_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : CoefficientRing O} (hP : IsAdmissible P) : conj H.compInv (conj H P) = P :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj (PowerSeries.constantCoeff_compInv H)
        (PowerSeries.isUnit_coeff_one_compInv H), reduction_conj hH hl,
      PowerSeries.map_compInv _ hH hl, LaurentSeries.conj_compInv_conj
        (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)
        ((isAdmissible_iff_reduction r P).mp hP)]

/-- Conjugation by `H` is injective on admissible elements of `A`. -/
theorem conj_inj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {P G : CoefficientRing O}
    (hP : IsAdmissible P) (hG : IsAdmissible G) : conj H P = conj H G ↔ P = G :=
  ⟨fun h ↦ by rw [← conj_compInv_conj hH hl hP, h, conj_compInv_conj hH hl hG],
    fun h ↦ h ▸ rfl⟩

/-- Conjugation preserves and reflects commutation: `H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`
commute if and only if `P` and `G` commute. -/
theorem conj_commute_iff (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P G : CoefficientRing O} (hP : IsAdmissible P) (hG : IsAdmissible G) :
    subst (conj H P) (conj H G) = subst (conj H G) (conj H P) ↔ subst P G = subst G P := by
  rw [← conj_subst hH hl hP hG, ← conj_subst hH hl hG hP,
    conj_inj hH hl (hG.subst hP) (hP.subst hG)]

end CoefficientRing

end FalseTateNonliftability

end CoordinateChange
