# Mathlib reuse

What the library takes from Mathlib, FontaineWintenberger and FalseTateExtension instead of
proving it here, what it used to prove and now takes from them, and what it proves that Mathlib
lacks (the `Mathlib/` directory, upstream candidates). Pinned versions: Mathlib `1e75e9d`,
FontaineWintenberger `7f43e30`, FalseTateExtension `2040c7e` (Lean `v4.35.0`). Keep this file
current when a pin moves.

## Used from Mathlib

| role | Mathlib |
|---|---|
| Laurent and power series | `LaurentSeries`, `HahnSeries` (`single`, `C`, `ofPowerSeries`, `orderTop`, `order`, `truncLT`, `leadingCoeff`), `PowerSeries` |
| Convergent sums `∑ aᵢ Gⁱ` in the construction of substitution | `HahnSeries.SummableFamily` (`hsum`, `single`, `mul`) |
| `R((T))` as `R⟦T⟧[1/T]`: a homomorphism out of `R((T))` from its values on `R⟦T⟧` and `T⁻¹` | `IsLocalization.Away.liftAlgHom`, `IsLocalization.ringHom_ext` |
| Substitution, composition and compositional inverse of power series | `PowerSeries.subst`, `PowerSeries.HasSubst`, `PowerSeries.subst_comp_subst_apply`, `PowerSeries.substInvOfIsUnit` (the project's `iterate`, `compInv`, `conj` are thin wrappers) |
| Derivatives | `LaurentSeries.derivative` (the Hasse derivative of order 1), `PowerSeries.derivative` |
| Topologies | `PowerSeries.WithPiTopology` (coefficientwise convergence on `κ⟦T⟧`), `LaurentSeries.valued` (the valued topology on `K((T))`, compared with the `T`-adic topology of `Mathlib/RingTheory/LaurentSeries/Topology`) |
| Coefficient rings of substitution | `IsLocalRing`, `IsArtinianRing`, `IsPrincipalIdealRing`, `isArtinianRing_iff_isNilpotent_maximalIdeal` (the truncations `O ⧸ 𝔪 ^ (r + 1)`) |
| Discrete valuation rings | `IsDiscreteValuationRing`, `IsDiscreteValuationRing.addVal` (`e = v(p)`), `IsDiscreteValuationRing.exists_irreducible` |
| The ring `A_K` | `AdicCompletion`, `AdicCompletion.evalₐ`, `IsAdicComplete` |
| `p`-adic numbers | `ℚ_[p]`, `ℤ_[p]`, `PadicInt.toZMod`, `PowerSeries.binomialSeries` (`(1 + X) ^ c` over `ℤ_p`, whose image in `κ⟦X⟧` defines `z ^ c`) |
| Finite fields and cyclic groups | `IsCyclic.exists_ofOrder_eq_natCard` (a generator of `𝔽_pˣ`), `ZMod.card_units`, `charP_of_card_eq_prime`, `frobenius` |

## Used from FontaineWintenberger

| role | FontaineWintenberger |
|---|---|
| The field of norms `X_K(L)` | `FieldOfNorms K L` with instances `Field`, `Valued _ ℤᵐ⁰`, `CharP`, `CompleteSpace`, discrete valuation ring; `FieldOfNorms.valuation`, `FieldOfNorms.uniformizer`, `FieldOfNorms.valuation_uniformizer` |
| `ev_u : κ_L((T)) ≅ X_K(L)` (Lemma 2.2) | `FieldOfNorms.laurentEquiv`, `laurentEquiv_C`, `laurentEquiv_X`, `continuous_laurentEquiv` |
| The action of `Aut(L/K)` on `X_K(L)` | `FieldOfNorms.aut`, `aut_valuation`, `continuous_aut_apply`, `mapEquiv_residueConstants` (the action fixes the constants) |
| Ramification numbers on `X_K(L)` and Wintenberger, Proposition 3.3.2 (Yuan (5.3)) | `FieldOfNorms.ramificationNumber`, `FieldOfNorms.ramificationNumber_eq_uniformizer`, `exists_finiteIntermediateField_ramificationNumber_eq` |
| APF hypothesis of Definition 1.1 | `IsAPF` |
| Rings of integers and residue fields | `𝒪[K]`, `𝓀[K]`, `spectralIntegerRing`, `integralClosureSpectralResidueEquiv`, `ramificationIdx_eq_addVal_uniformizer`, `irreducible_of_valuation_exp_neg_one` |
| Teichmüller representatives (definition of `δ`) | `residueTeichmuller` |

## Used from FalseTateExtension

| role | FalseTateExtension |
|---|---|
| `ℚ_p^FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` | `falseTateExtension p π` and its instances `IsGalois`, `IsAPF`; `not_finiteDimensional_falseTateExtension_padic`; `falseTateExtension_residue_algebraMap_surjective` |
| `τ` and Lemma 1.2 (2), (3) | `kummerGenerator` (notation `τ`), `kummerKernelEquivPadicInt` (`ker χ ≅ ℤ_p`, so `τ^a` for `a ∈ ℤ_p`), `padicKummerExponent`, `padicCyclotomicCharacter`, `falseTateKummerFixing`, `kummerFixingEquivCyclotomicImage`, `cyclotomicExtensionCharacter_surjective_padic` |
| Proposition 5.1 on the finite layers (Viviani, Corollary 6.10, Remark 5.2) | `kummerRamificationBreak`, `kummerRamificationBreak_growth`, `kummerRamificationBreak_succ_dvd`, `ramificationOrder_tauPowRestrict` |
| `ℚ_p` as a local field | `padicResidueFieldEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p`, `padicValuationSubringEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p]` |

## Interfaces supplied by this library

`Liftability/TotallyRamified` provides `FontaineWintenberger.integralClosureResidueField`,
`FontaineWintenberger.IsTotallyRamified`, `IntermediateField.HasSameResidueField` and its
`residueFieldEquiv`. Their proofs use the integral closure and spectral residue field maps from
FontaineWintenberger's `APF/Tower/AlgebraicResidue`. These interfaces were removed upstream.
The false Tate total ramification instance in `FalseTate/RamificationNumbers` follows from
`falseTateExtension_residue_algebraMap_surjective`; the uniformizer instance
`Fact (Irreducible (p : 𝒪[ℚ_[p]]))` in `FalseTate/Main` follows from `PadicInt.irreducible_p`.

## Formerly proved here, now taken from upstream

| was | now |
|---|---|
| `normLimitMap_sourceResidueConstants_fixed` (the Galois action fixes the constants of the field of norms) | FontaineWintenberger `FieldOfNorms.mapEquiv_residueConstants` |
| `sourceNormFieldCoordinate → normFieldCoordinate → bergerCoordinateFamily` (three layers moving coefficients `κ_L → κ_K → κ_E`) and the `ZMod p → κ_F` transport of §4 | `CoordinateFamily.map` over FontaineWintenberger's `FieldOfNorms.laurentEquiv`; §4 is proved over every finite field of characteristic `p` |
| The `ℚ_p`-specific coordinates and ramification of the old FalseTateExtension `Padic/NormField*` modules (deleted upstream) | FontaineWintenberger's general field-of-norms API and Wintenberger, Proposition 3.3.2, plus FalseTateExtension's `ramificationOrder_tauPowRestrict` |
| The Teichmüller construction of the old FalseTateExtension `Padic/TameUnits` | FontaineWintenberger `residueTeichmuller` |
| `padicBinomialSeries` as an independent series | the image of Mathlib's `PowerSeries.binomialSeries ℤ_[p] c` |
| A private copy of `continuous_algHom_ext_X` and the unfolding of `SummableFamily.coeff_support` under `backward.isDefEq.respectTransparency false` | `Mathlib/RingTheory/LaurentSeries/Topology` and `Finsupp.mem_support_iff` |

## Upstream candidates (`FalseTateNonliftability/Mathlib/`)

Mathlib names and namespaces, importing only Mathlib. Checked absent from the pinned Mathlib.

| file | content |
|---|---|
| `Algebra/CharP/CharAndCard` | `charP_of_natCard_eq_prime`: a ring with `p` elements has characteristic `p` (the `Nat.card` form of `charP_of_card_eq_prime`) |
| `NumberTheory/Padics/Continuity` | `PadicInt.continuous_toZMod`; `PadicInt.exists_tendsto_of_prime_mul_tendsto`: if `p xₙ → b` in `ℤ_p`, then `xₙ → b / p` |
| `RingTheory/AdicCompletion/Quotient` | `AdicCompletion.ker_evalₐ_eq_map_pow`: for finitely generated `I`, the kernel of `R̂ → R ⧸ Iⁿ` is `Iⁿ R̂`; `AdicCompletion.factor_evalₐ` |
| `RingTheory/LaurentSeries/Derivative` | Leibniz and power rules for `LaurentSeries.derivative` (coefficient proofs), derivatives in characteristic `p` (`exists_derivative_iff`, `derivative_eq_zero_iff_exists_pow`) and the primitive `coefficientPrimitive` |
| `RingTheory/LaurentSeries/Topology` | the `T`-adic topology `orderTopology R` on `R((T))` over any commutative ring (scoped instance, Hausdorff ring topology), convergence of truncations, `continuous_ringHom_ext`, `continuous_derivative`, `orderTopology_eq_valued` |
| `RingTheory/LaurentSeries/Map` | the coefficient map `LaurentSeries.mapRingHom` and its order, continuity and derivative; `R((T)) ⧸ (a) ≃+* (R ⧸ (a))((T))` (`principalQuotientEquiv`) |
| `RingTheory/PowerSeries/Compactness` | the units of `κ⟦T⟧` are closed, and compact for finite `κ`; convergent subsequences of units |
| `RingTheory/PowerSeries/Composition` | `PowerSeries.iterate`, `PowerSeries.compInv`, `PowerSeries.conj` and their algebra; low-degree coefficients of `f ∘ g` and `f^{∘n}`; compatibility with coefficient maps |

Declarations in Mathlib namespaces that depend on the project's Laurent substitution
(`LaurentSeries.subst`, `PowerSeries.ramificationNumber`, `PowerSeries.principalUnitPow`, the §4
results) stay in their layers; they would follow `LaurentSeries.subst` upstream.
