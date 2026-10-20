# FalseTateNonliftability 升级与重构方案（v0 草案，待逐条讨论）

> 状态：**草案，尚未执行**。按 FontaineWintenberger / FalseTateExtension 的做法，A–I 逐节与作者讨论定稿后再按 §I 分阶段执行；每阶段一个分支。
>
> 范围 = instruction.pdf §3：形式化 FalseTateLift.pdf 的 Theorem A（含 Definition 1.1、Proposition 1.3、Proposition 2.3）。
>
> 本文的"现状"指提交 `9a13337`（2026-10-19），依赖 FW `7a8d63c`（Init commit）、FTE `7d6876c`、Mathlib `f0b4c81`。目标依赖：FW `b7d6a18`、FTE `817737a`、Mathlib `1e75e9d`（FTE 已钉此版本）。

---

## 0. 现状数据（2026-10-20 实测）

| 指标 | 数值 |
|---|---|
| Lean 文件 | 40 模块 + 根文件，四个目录平铺（`LaurentSeries/` 20、`CoefficientRing/` 12、`PowerSeries/` 4、`FieldOfNorms/` 2、`FalseTate/` 2） |
| 总行数 | 12 400 |
| 声明数 | 688（theorem/lemma 594，def/abbrev/structure/instance 73；`private` 41） |
| **从未被其他文件引用的声明** | **418 / 688**（NormalizedDerivative 43、NormalForm 36、CoefficientRing/Substitution 28、FieldOfNorms/CoordinateChange 26、TheoremA 24、PrincipalUnitPowers 21、Graded 20、Truncation 20） |
| 干净全量编译（旧依赖，20 核） | 6 min 50 s 墙钟 / 290 s CPU（本项目 41 个模块；总 4000 个 job 中其余是 Mathlib/FW/FTE 的 replay） |
| 单文件 > 30 s | 1 个：`FalseTate/TheoremA`（lake 31 s；`lake env lean` 58 s） |
| 10–20 s | `FieldOfNorms/Liftability` 15、`FieldOfNorms/CoordinateChange` 15、`PowerSeries/PrincipalUnitPowers` 11、`CoefficientRing/FiniteObstruction` 10 |
| `set_option maxHeartbeats` | 0；但 `PowerSeriesEval.lean:39` 有一处 `set_option backward.isDefEq.respectTransparency false` |
| `letI`/`let :=` 出现在**定理陈述**里 | TheoremA 7 处、FieldOfNorms/Liftability 5、FieldOfNorms/CoordinateChange 6、DerivativeLevel 1、CoefficientRing 若干（`let : CharP … := …` 进陈述） |
| 陈述里内联的 tactic/证明项 | `powerSeriesSubstEquiv 0 IsNilpotent.zero f hf (by rw [hlinear]; exact isUnit_one)` ≥ 15 处；`residue π hπ (e + 1) (by omega)` 53 处；`IsNilpotent.zero` 显式传递 61 处 |
| 同一 `local instance : (Ideal.span {(0:k)}).IsMaximal` 的拷贝 | 21 处（7 个 LaurentSeries 文件 + 14 处 CoefficientRing/PowerSeries） |
| `let := parameter_isMaximal π hπ r hr` | 48 处 |
| 显式 `(hπ : Irreducible π)` / `(hp₂ : p ≠ 2)` | 30 / 2（但 `hp₂ hπ` 作为参数穿过 TheoremA 全部 30 条声明） |
| `nlinarith` / `convert` / `erw` | 12 / 8 / 2 |
| `Classical.choose` 定义的数据 | `subst`（Substitution:62）、`derivativeLevel`、`normalizedDerivative`（NormalizedDerivative:451/469）、`sourceNormFieldCoordinate`（FieldOfNorms/Liftability:210）等 12 处 |
| 文档填充词 actual / original / canonical / ordinary / genuine / prescribed / existing / intrinsic / literal | 509 / 201 / 86 / 21 / 16 / 12 / 12 / 9 / 5（合计 ≈ 880） |
| 悬空引用 | 40 处 `nl:*` / `ft:*` blueprint 标签（仓库无 `blueprint/`）；根文件指向不存在的 `blueprint/src/content.tex`；16 处 "Yuan, Lemma 2.3 / 4.1 / Prop 4.2 / §6 (6.1)"，**编号与论文不符**（论文是 Lemma 2.4 / 4.1 / 4.2、Prop 4.3） |
| 版权头 / LICENSE / README / CLAUDE.md / docs | **全部缺失**（40 个文件无版权头） |
| 超过 100 字符的行 | 85 |
| 仓库 lakefile 开启 `weak.linter.mathlibStandardSet = true` 后的警告 | 40 个 header 警告 + 85 个 longLine 警告（基准编译是在 fw-workspace 的无 `leanOptions` 的 lakefile 下做的，所以显示 0 警告；**在本仓库 CI 下会违反 instruction §4(7)**） |
| 根目录 `*.pdf` | 两个 PDF 未被 `.gitignore`，处于未跟踪状态 |

关于"编译慢"的实测结论：基准日志里 `CharacteristicP` 112 s、`PrincipalQuotient` 135 s、`NilpotentPower` 136 s、`OrderTopology` 136 s、`PrincipalUnitIntegerPowers` 176 s 这五个数字是**测量伪影**——它们是并行构建里最先碰到的叶子模块，把 Mathlib olean 的首次加载时间算了进去；逐个重测（热缓存）都是 2 s。真正的热点只有 `TheoremA`（31–58 s，原因见 §F）。本项目自身的编译时间（≈ 5 min CPU）不是主要负担；作者感到的慢更可能来自 (1) 每次 `lake build` 需要 replay FW + FTE 共 ~290 个模块，(2) 任一基础文件改动都会触发大范围重编（见 §F 的分层倒置）。

---

## A. 依赖升级（FW `7a8d63c` → `b7d6a18`，FTE `7d6876c` → `817737a`，Mathlib `f0b4c81` → `1e75e9d`）

### A1. 影响面

本项目只有 6 个文件 import 上游：`FieldOfNorms/Liftability`、`FieldOfNorms/CoordinateChange`、`FalseTate/TheoremA`、`CoefficientRing/{Truncation, NormalizedDerivative, FiniteObstruction}`。但 TheoremA 一个文件就用了 FTE 已删除的三个 NormField 模块的 21 个声明。Mathlib 只前进 23 个提交（10-15 → 10-16），预计无实质破坏。

### A2. 上游已删除、本项目正在使用的模块（必须在本项目重做）

FTE 的 F2 阶段（提交 `914e144`）按其方案 A1 把属于 instruction §3 的内容整体删除（不进 Attic），本项目是唯一消费者：

| 旧 FTE 模块（行数） | 本项目用到的声明 | 数学内容 | 去向 |
|---|---|---|---|
| `Padic/NormFieldCoordinates`（496） | `falseTateResidueEquiv`、`falseTateNormCoefficients`、`falseTateNormFieldLaurentEquiv(_unique, _powerSeriesCoordinate)`、`falseTateLaurentAction(_powerSeries)`、`falseTatePowerSeriesCoordinate(_constantCoeff, _linear_isUnit, _mul, _pow)` | 把 `X_{ℚ_p}(K_FT)` 和 `𝔽_p((T))` 用一个 uniformizer 等同，Galois 元的坐标级数 `f_{g,u}`（论文 §1.4、Lemma 2.2） | **不再按 ℚ_p 特例重做**。本项目 `FieldOfNorms/Liftability.lean` 已有对任意 APF `L/K`（剩余域平凡）的一般版本 `sourceNormFieldCoordinate`；升级后直接用 FW 的 `FieldOfNorms.laurentEquiv`/`FieldOfNorms.aut`，特例化到 `K = ℚ_p` 只需 `padicResidueFieldEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p`（FTE `Padic/Basic`）。TheoremA 里 150 行把两套坐标对齐的代码（`sourceNormFieldCoordinate_falseTate`、`bergerCoordinateFamily_falseTate`、`normLimitLaurentEquiv_map_falseTateResidueEquiv`）随之消失。 |
| `Padic/NormFieldRamification`（353） | `not_finiteDimensional_falseTateExtension_padic`（15 处） | `d_k = i_E(τ^{p^k})`（Prop 5.1 的 (5.3) 步：对角层共尾 + 手工把 norm-field 作用的位移转到有限层） | `not_finiteDimensional_…` 已移到 FTE `Cyclotomic/InfiniteCharacter`。`d_k` 的计算**改走新路**：FW 现在有 Wintenberger Prop 3.3.2 `exists_finiteIntermediateField_ramificationNumber_eq`（`FieldOfNorms/Estimates/Transfer`，即论文 (5.3)）和 `FieldOfNorms.ramificationNumber`（即 `i_E(g)`），FTE 有 `ramificationOrder_tauPowRestrict`/`normalizedValuation_tauPowRestrict_displacement`（`τ^{p^k}` 在 `L_N`（`N ≥ k+2`）上的下分歧数 `d_k + 1`）。新文件 `FalseTate/RamificationNumbers.lean` 只需把 FW 的 `FiniteIntermediateField.ramificationNumber`（嵌入版，`EReal`）与 FTE 的 `ramificationOrder`（Serre 的 `i_G`，在 `falseTateDiagonalLayer`）对接。 |
| `Padic/NormFieldAction`（484） | `falseTatePowerSeriesCoordinate_tau_pow_order`、`_tau_infiniteOrder`、`_tau_coeff_one`、`orderOf_…_tameGenerator_linear_unit` | Prop 5.1 在坐标级数上的表述；Lemma 5.3（δ 的线性系数 = χ(δ) mod p，阶 p−1，经 δτδ⁻¹ = τ^{χ(δ)} 与作用的连续性） | 重做为 `FalseTate/TameGenerator.lean`（Lemma 5.3）。连续性用 FW `FieldOfNorms.continuous_aut_apply`（`Galois/Action`）；`τ^a`（`a ∈ ℤ_p`）用 FTE `kummerKernelEquivPadicInt : ker χ ≃ₜ+ ℤ_[p]`；`b(δτδ⁻¹) = χ(δ)` 用 FTE `padicKummerExponent_mul`。 |
| `Padic/TameGenerator`（175）、`Padic/TameUnits` | `tameGenerator`（7 处） | δ：`Gal(K_FT/K_Kum)` 中的挠生成元（经 Teichmüller 提升构造） | **简化**：Lemma 5.3 的证明只用到 `χ(δ) mod p` 在 `𝔽_p^×` 中阶为 `p−1`，不需要 δ 本身是挠元。取 `δ ∈ Gal(K_FT/K_Kum)`（FTE `falseTateKummerFixing`）为 `kummerFixingEquivCyclotomicImage`/`cyclotomicExtensionCharacter_surjective_padic` 下任一 `u ∈ ℤ_p^×` 的原像，`u mod p` 为生成元即可；Teichmüller 整套不再需要。定义名 `tameGenerator`（记号 `δ`），docstring 写明"任一剩余特征为 `𝔽_p^×` 生成元的 Kummer 固定元"。 |
| `Padic/KummerRamification` §PadicLimit | `kummerRamificationLimit`（9）、`kummerRamificationDenominator`、`kummerRamificationBreak_tendsto_padic`、`kummerRamificationLimit_ne_intCast`（本项目已有一份） | `d_k → (p−1)/(p+1) ∈ ℤ_p ∖ ℤ`（Prop 5.1 (2)） | 在 `FalseTate/RamificationNumbers.lean` 重建（≈ 60 行）。`kummerRamificationBreak` 及 `_growth`、`_succ_dvd`、`_tendsto_real` 保留在 FTE `FalseTate/Viviani/TauRamification`。 |
| `Padic/CyclotomicRamification` | `padicUnitBallEquiv` | `𝒪[ℚ_p] ≃+* ℤ_[p]` | FTE `Padic/Basic.padicValuationSubringEquiv`。注意 `CoefficientRing/Truncation.lean:5` import 了这个模块但**一个声明也没用**，删 import。 |

FW 侧的改名（本项目用到的）：

| 旧 | 新 | 备注 |
|---|---|---|
| `NormLimit K L`；`normLimitField/Valued K L p hL hInf`（`letI` 安装 21 处） | `FieldOfNorms K L`，`Field`/`Valued _ ℤᵐ⁰`/`CharP`/`CompleteSpace`/DVR 全是 instance | 所有 `letI := normLimitField …` 删除 |
| `normLimitValuation K L hL` | `FieldOfNorms.valuation K L` | |
| `normLimitUniformizer`、`normLimitValuation_normLimitUniformizer` | `FieldOfNorms.uniformizer`、`FieldOfNorms.valuation_uniformizer` | |
| `normLimitLaurentEquiv K L p hL hInf u hu`（+ `_C`、`_X`、`_valuation`、`continuous_`） | `FieldOfNorms.laurentEquiv K L u hu`（`Structure/Laurent`）、`laurentEquiv_C/_X/_valuation`、`continuous_laurentEquiv`、`laurentEquiv_unique` | 新的 `laurentEquiv_unique` 正是旧 FTE `falseTateNormFieldLaurentEquiv_unique` 的一般版 |
| `normLimitAut K p hL hInf g`、`normLimitAut_valuation` | `FieldOfNorms.aut K L g`、`aut_valuation`（`Functor/Map`） | |
| `normLimitMap`、`normLimitEval`、`NormLimit.ext`、`normLimitEval_norm`、`coe_normLimitEval_normLimitMap` | `FieldOfNorms.mapEquiv`、`FieldOfNorms.coord`、`FieldOfNorms.ext`、`coord_inclusion`、`coord_mapEquiv` | 只在 `normLimitMap_sourceResidueConstants_fixed` 一条证明里用 |
| `sourceResidueConstants(FieldEmbedding)`、`sourceResidueCoordinate`、`sourceResidueRoot`、`normLimitEval_sourceResidueConstants` | `residueConstants(FieldEmbedding)`、`residueCoordinate`、`residueRoot`、`coord_residueConstants`（`Structure/ResidueEmbedding`） | **FW 已有 `FieldOfNorms.mapEquiv_residueConstants`（`Estimates/Transfer:426`）**：Galois 作用固定常数——本项目 `normLimitMap_sourceResidueConstants_fixed` 的 25 行证明可删 |
| `FiniteLayer`、`FiniteLayer.sup/map` | `FiniteIntermediateField` | |
| `apfMaximalUnramified K L hL` 等 | `apfMaximalUnramified K L`（`[IsAPF K L]`） | |
| `IsAPF K L` 作 `hL` 显式参数 / `Fact (IsAPF K L)` | `[IsAPF K L]` class | 本项目 `BergerLiftable` 用了 `[Fact (IsAPF K L)]`，改掉 |
| `hInfinite : ¬ Module.Finite K L` / `Fact (¬ Module.Finite K L)` | `[Fact (¬ Module.Finite K L)]` | 一致，保留 |
| `(NormedField.valuation (K := K)).valuationSubring`、`IsLocalRing.ResidueField (…)`、`local notation "R"/"κK"/"O_F"/"O_0"/"O_E"` | `𝒪[K]`、`𝓀[K]`（FW scoped notation；`open scoped FontaineWintenberger`） | 本项目 44 条 `local notation` 里约 20 条是这类 |
| `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsDiscreteValuationRing …] [PerfectField …]` + `(p) [Fact p.Prime] [CharP 𝓀 p]` | `[NontriviallyNormedField K] [IsPerfectResidueLocalField K]`，`p := residueChar K`；或在 p 进层按 FTE 约定保留显式 `p` 并用 `residueChar_padic`/`residueChar_eq` 对接 | 见 §C3 |
| `Padic p`、`PadicInt p` | `ℚ_[p]`、`ℤ_[p]` | |
| `spectralIntegerRing (Padic p) F` | 保留 `spectralIntegerRing ℚ_[p] F`（FTE A2.2 试过 `𝒪[F]` 失败） | |
| `residueTeichmuller R p`、`spectralTeichmuller` | 同名，位置 `Ramification/Lower/Teichmuller` | 只在 `sourceResidueCoordinate_mem_base` 用；若改用 `mapEquiv_residueConstants` 则不再需要 |
| `LocalField.LaurentSubstitution.map_ofPowerSeries_eq_subst` | `Mathlib/Topology/LaurentSubstitution`（同名） | 还新增了 `comp_apply_parameter`、`iterate_apply_parameter_eq_subst_iterate`，正是本项目 `sourceNormFieldCoordinate_mul/_pow` 要证的东西 |
| `valuedRingEquiv_uniformContinuous` | `Mathlib/Analysis/UniformContinuity`（同名） | |
| `extensionValuationSubring_ramificationIdx_mul_residueDegree` | `Ramification/Lower/Degree`（同名） | |
| `spectralIntegerRing_moduleFinite` | `LocalField/Spectral/FiniteExtension`（同名） | |
| `integralClosureSpectralResidueEquiv`、`integralClosure_algebraMap_isLocalHom` | `APF/Tower/AlgebraicResidue` | |

FTE 侧：

| 旧 | 新 |
|---|---|
| `tau p hp₂ hπ`（`.val` 取群元） | `kummerGenerator p π`，scoped notation `τ`（`open scoped FalseTateExtension.FalseTate`，须核实命名空间）；`[Fact (p ≠ 2)] [Fact (Irreducible π)]`，`π : 𝒪[K]` 显式 |
| `isAPF_falseTateExtension p hπ` | instance |
| `falseTateExtension_isGalois p π hπ₀` | instance（`[NeZero π]`，由 `Fact (Irreducible π)` 推出） |
| `falseTateExtension_residue_algebraMap_surjective p hp₂ hπ` | 同名，`FalseTate/TotalRamification`，instance 参数 |
| `padicCyclotomicCharacter p π g` | 同名（`Coordinates/Padic`，现为 `abbrev`，对任意特征 0 的 K） |
| `kummerRamificationBreak p k`（+ `_growth hp`、`_succ_dvd`） | 同名，`FalseTate/Viviani/TauRamification` |

### A3. 升级顺序与验证

1. 先只改 `lakefile.toml`/`lake-manifest.json` 到目标版本，`lake build` 看破坏面（预计：上表全部 + Mathlib 的零星改名）。这一步不修代码，只记录错误清单，作为 §I 阶段 U1 的输入。
2. FW 目标 `b7d6a18` 是 merge commit，树与 `6c9e973` 相同；FTE 的 manifest 已钉 `b7d6a18`，本项目 manifest 要与之一致，否则 lake 报 "dependency mismatch"。
3. 升级与重构**不混做**：U1 阶段只做"编译通过的最小改动"（改名、删 `letI`、重建 A2 表里的 4 个模块），然后再进入重构阶段。否则无法区分破坏是升级还是重构造成的。

---

## B. liftable 条件的翻译（Definition 1.1 / Proposition 1.3 / Proposition 2.3）

### B1. 现状

现有定义分三层：

```lean
-- CoefficientRing/Liftability.lean
structure CompletedLift (π : O) (hπ : Irreducible π) (f : Γ → PowerSeries κ) (hfzero : …) (hflinear : …) where
  P : PrincipalCompletion π                 -- AdicCompletion (span {C π}) (LaurentSeries O)
  F : Γ → PrincipalCompletion π
  residue_P : completedResidue π hπ P = HahnSeries.single (Nat.card κ) 1
  residue_F : ∀ g, completedResidue π hπ (F g) = ofPowerSeries (f g)
  commute   : ∀ g, completedSubst π hπ P (proof…) (F g) = completedSubst π hπ (F g) (proof…) P
  composition : ∀ g h, completedSubst π hπ (F g) (proof…) (F h) = F (g * h)
def Liftable π hπ f hfzero hflinear : Prop := Nonempty (CompletedLift …)
-- FieldOfNorms/Liftability.lean
def BergerLiftable K L E : Prop :=
  letI … ; let hL := Fact.out ; let hInfinite := Fact.out ; let hres := Fact.out ; let u := normLimitUniformizer … ; let hu := …
  ∃ (ε : κE ≃+* κK) (ϖ : O_E) (hϖ : Irreducible ϖ), Liftable ϖ hϖ (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε) (…) (…)
-- FalseTate/TheoremA.lean
theorem falseTate_not_bergerLiftable : letI := … ; letI : Fact (IsAPF …) := … ; letI : Fact (¬ Module.Finite …) := …
    ¬ @BergerLiftable p _ (Padic p) _ _ _ _ _ _ FT _ _ _ _ _ ⟨falseTate_integralClosureResidue_surjective p hp₂ hπ⟩ F _ _ _
```

与论文 Definition 1.1 逐条对照：

| 论文 | 现状 | 问题 |
|---|---|---|
| `F/ℚ_p` 有限，剩余域与 `K` 相同（`𝔽_q`） | `E` 任意有限扩张 + `∃ ε : κ_E ≃+* κ_K` | (i) "相同剩余域"被翻译成"存在某个同构"。`κ_E ≃+* κ_K` 的同构之间差一个 Frobenius 幂，不同 ε 给出不同的 `f_g` 系数；定义里 `∃ ε` 使"F-liftable"比论文弱（论文隐含固定了等同），从而 `¬ BergerLiftable` 比 Theorem A 强。Theorem A 情形剩余域是 `𝔽_p`，ε 唯一，所以结论没错，但定义本身不忠实。 |
| `A_K` = `𝒪_F⟦T⟧[1/T]` 的 `ϖ_F` 进完备化 | `PrincipalCompletion ϖ := AdicCompletion (span {C ϖ}) (LaurentSeries 𝒪_F)`，再 `∃ ϖ, Irreducible ϖ` | (ii) `A_K` 不依赖 uniformizer 的选取（`ϖ` 进 = `p` 进 = 极大理想进），定义里却对 `ϖ` 取存在量词，并且 `Irreducible ϖ` 作为显式证明参数穿过全部 `CoefficientRing/` 声明（`π hπ` 二元组出现在约 180 条声明里）。 |
| `P̄ = T^q` | `completedResidue P = single (Nat.card κ) 1`，`[Finite κ]` | 忠实。 |
| `ev_u(F̄_g) = g ∗ u`，`u` 为 `X_K(L)` 的 uniformizer | `residue_F g = ofPowerSeries (f g)`，`f = bergerCoordinateFamily … (normLimitUniformizer …)`：`f` 是经 `κL → κK → κE` 三次系数搬运后的 `sourceNormFieldCoordinate`，后者由 `Classical.choose` 从 `exists_powerSeries_coordinate_of_valuation` 取出 | (iii) 数学上对；工程上 `FieldOfNorms/Liftability.lean` 480 行 + `FieldOfNorms/CoordinateChange.lean` 760 行几乎全是这三层搬运的簿记（`normFieldCoordinate`、`bergerCoordinateFamily` 各自重复 `_constantCoeff/_linear_isUnit/_mul/_pow/_one/_eval` 一套）。 |
| `F_g ∘ P = P ∘ F_g`，`F_h ∘ F_g = F_{gh}` | `commute`、`composition`（`completedSubst G J` 表示 `J ∘ G`，方向正确） | 忠实。但每个 `completedSubst` 都要带一个 admissibility 证明项，于是 `commute` 字段的**类型**里含 `completedIsAdmissible_of_residue_card_monomial π hπ P residue_P` 这样的证明项——字段之间互相依赖，`CompletedLift.conjugate` 等构造必须逐字段重证这些证明项相等。 |
| `L/K` 的 Galois 群 `Γ` 作用在 `X_K(L)` 上 | `Γ` 抽象群 + `f : Γ → PowerSeries κ` + 两条逐点性质作参数；`FieldOfNorms` 层用 `L ≃ₐ[K] L` | 抽象层设计本身好（Def 1.1 对任意 `p` 进 Lie 扩张），但"坐标族"没有打包成一个对象，`f hfzero hflinear` 三件套在 95 条声明里穿行。 |
| 论文默认 `L/K` 完全分歧（`k_L = 𝔽_q`） | `[Fact (Function.Surjective (algebraMap 𝓀[K] κL))]` | (iv) 以 `Fact` 包一个 60 字符的命题，再在 Theorem A 的陈述里用 `⟨falseTate_integralClosureResidue_surjective p hp₂ hπ⟩` 显式喂进 `@BergerLiftable` 的第 15 个参数。 |
| Prop 1.3：`R = A/ϖ^{e+1}` 中不存在 `P, F_τ, F_δ` 满足约化条件与两条交换关系（**无**合成律，只有三个元素） | `falseTate_finite_obstruction`：`let f := …; ∃ e, addVal p = e ∧ ∀ P hP G D hG hD, (truncatedSubst … P (proof) G = truncatedSubst … G (proof) P) → … → False`，另有 `FiniteLift`（整族 + 合成律）和 `FiniteLiftable` | (v) Prop 1.3 没有一条干净的陈述；`FiniteLiftable`（整族）与论文 Prop 1.3（三元）是两个不同命题，论文的那个更强，代码里反而只是中间产物。 |
| Prop 2.3：F-liftability 与 uniformizer 无关，对任意 `ϖ_F` 幂的模与任意子集同样成立 | `bergerLiftable_iff_uniformizer`、`_iff_exists_uniformizer`、`_iff_forall_uniformizer`、`bergerCoordinateFamily_(finite)liftable_iff` | 内容在，但陈述各带 6–8 个 `Fact.out` 记号；"任意子集"版本没有。 |
| Theorem A | `falseTate_not_bergerLiftable`：陈述含 3 个 `letI`、14 个 `_`、`hp₂ hπ htotal` 三个显式证明参数 | (vi) 不可读；`htotal`（`F/ℚ_p` 完全分歧）以 `ramificationIdx = finrank` 的等式形式给出，而 FTE/FW 都没有 `IsTotallyRamified` 类——需要决定。 |

### B2. 建议的新翻译（待讨论）

```lean
namespace FalseTateNonliftability

/-- Definition 1.1. The coefficient ring `A_K`: the `𝔪_F`-adic completion of `𝒪_F⟦T⟧[1/T]`,
modelled as the adic completion of `𝒪_F((T))` at the ideal generated by the constants `𝔪_F`.
It depends on `F` only. -/
abbrev CoefficientRing (O : Type*) [CommRing O] [IsLocalRing O] : Type _ :=
  AdicCompletion ((IsLocalRing.maximalIdeal O).map HahnSeries.C) (LaurentSeries O)
-- 对 DVR 与 `span {C ϖ}` 相同（`maximalIdeal = span {ϖ}`），但定义里不再出现 ϖ。
-- 截断：`LaurentSeries (O ⧸ 𝔪^(r+1))`，用 `r + 1` 索引，消灭 `hr : 1 ≤ r` 与 `(by omega)`。

/-- The coordinate series `(f_g)_{g ∈ Γ}` of an action of `Γ` on `κ((T))` by continuous
`κ`-automorphisms preserving the valuation: `f_g ∈ T κ⟦T⟧` with unit linear coefficient and
`f_{gh} = f_h ∘ f_g` (Lemma 2.2). -/
structure CoordinateFamily (κ : Type*) [Field κ] (Γ : Type*) [Group Γ] where
  series : Γ → PowerSeries κ
  constantCoeff_eq_zero : ∀ g, (series g).constantCoeff = 0
  isUnit_coeff_one : ∀ g, IsUnit ((series g).coeff 1)
  series_mul : ∀ g h, series (g * h) = (series h).subst (series g)

/-- A lift of a coordinate family to `A_K` (Definition 1.1, conditions 1 and 2). -/
structure CoordinateFamily.Lift (f : CoordinateFamily (ResidueField O) Γ) where
  frobenius : CoefficientRing O
  lift : Γ → CoefficientRing O
  residue_frobenius : residue frobenius = X ^ Nat.card (ResidueField O)
  residue_lift : ∀ g, residue (lift g) = f.series g
  commute : ∀ g, lift g ∘ frobenius = frobenius ∘ lift g      -- `∘` := 以 `IsAdmissible` 为 Prop 的 `subst`，不带证明参数（见 C1）
  lift_mul : ∀ g h, lift h ∘ lift g = lift (g * h)

def CoordinateFamily.Liftable (f) : Prop := Nonempty f.Lift
/-- The same conditions modulo `𝔪_F^(r+1)` for the elements of a subset `S ⊆ Γ` and **without**
the composition law — the shape of Proposition 1.3. -/
def CoordinateFamily.FiniteLiftable (f) (S : Set Γ) (r : ℕ) : Prop := …
theorem CoordinateFamily.Liftable.finiteLiftable : f.Liftable → f.FiniteLiftable S r      -- ⊇ 现 `Liftable.finite`
theorem CoordinateFamily.liftable_conj_iff (w : PowerSeries κ) … : (f.conj w).Liftable ↔ f.Liftable   -- Prop 2.3 抽象版，含 FiniteLiftable 版
```

field-of-norms 层：

```lean
variable (K) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
  (L) [Field L] [Algebra K L] [IsGalois K L] [IsAPF K L] [Fact (¬ Module.Finite K L)]
  [IsResidueTrivial K L]        -- 新 Prop class：`algebraMap 𝓀[K] 𝓀_L` 满射（= 完全分歧，论文的隐含假设）；见 B3 问题 2

/-- Lemma 2.2: the coordinate family of `Gal(L/K)` on `X_K(L)` in the uniformizer `u`, with
coefficients in `𝓀[K]`. -/
def FieldOfNorms.coordinateFamily (u) (hu : valuation u = exp (-1)) : CoordinateFamily 𝓀[K] (L ≃ₐ[K] L)

/-- Definition 1.1: the action of `Gal(L/K)` on `X_K(L)` is `F`-liftable, for `F/ℚ_p` finite
with residue field identified with `𝓀[K]` by `ε`. -/
def IsLiftable (F) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (ε : 𝓀_F ≃+* 𝓀[K]) : Prop :=
  ((FieldOfNorms.coordinateFamily K L (FieldOfNorms.uniformizer K L) _).mapResidue ε.symm).Liftable
theorem isLiftable_iff_uniformizer (u hu) : IsLiftable K L F ε ↔ (… u hu …).Liftable   -- Prop 2.3
```

Theorem A / Prop 1.3：

```lean
variable (p) [Fact p.Prime] [Fact (p ≠ 2)] (π : 𝒪[ℚ_[p]]) [Fact (Irreducible π)]
  (F) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsTotallyRamified ℚ_[p] F]   -- 见 B3 问题 3

/-- Proposition 1.3. -/
theorem not_finiteLiftable_falseTate (ε : 𝓀_F ≃+* 𝓀[ℚ_[p]]) :
    ¬ (… coordinateFamily …).FiniteLiftable {τ, δ} (absoluteRamificationIdx p F)   -- 模 ϖ^{e+1}，索引 r+1 = e+1
/-- Theorem A. -/
theorem not_isLiftable_falseTate (ε : 𝓀_F ≃+* 𝓀[ℚ_[p]]) :
    ¬ IsLiftable ℚ_[p] (falseTateExtension p π) F ε
```

（`𝓀[ℚ_[p]] ≃+* ZMod p` 下 `ε` 唯一，所以 `∀ ε` 与 `∃ ε` 在这里等价；按 B3 问题 1 的决定，Theorem A 的陈述可能干脆不带 `ε`。）

### B3. 需要作者拍板的问题

1. **剩余域等同 `ε` 的量词**。(a) 作为 `IsLiftable` 的显式参数（最忠实于"同一个剩余域"；Theorem A 对所有 `ε` 陈述）；(b) 定义里 `∃ ε`（现状；`¬` 最强，但定义偏弱）；(c) 把 `𝓀_F` 与 `𝓀[K]` 的等同做成 instance `[Algebra 𝓀[K] 𝓀_F] [IsScalarTower …]`——过重。**建议 (a)**。
2. **"`L/K` 完全分歧"的表达**。现状 `Fact (Surjective (algebraMap 𝓀[K] κL))`。建议新 Prop class `IsResidueTrivial K L`（或叫 `HasTrivialResidueExtension`），实例 `[IsResidueTrivial ℚ_[p] (falseTateExtension p π)]` 由 FTE `falseTateExtension_residue_algebraMap_surjective` 给出。替代：把它并进 Def 1.1 的前提列表里显式写。**建议 class**。
3. **"`F/ℚ_p` 完全分歧"的表达**。现状 `htotal : ramificationIdx = finrank` 显式等式。选项：(a) Prop class `IsTotallyRamified ℚ_[p] F`（FTE 目标 (5) 也是用 `residueDegree = 1`/`ramificationIdx = finrank` 两条定理陈述的，没有 class）；(b) 直接假设 `Finite 𝓀_F ∧ Nat.card 𝓀_F = p`，即"剩余域是 `𝔽_p`"——这正是论文 §1.3 说的"these coefficient fields are precisely the finite totally ramified extensions"，而且证明里只用到剩余域 = `𝔽_p`；(c) 维持等式。**建议 (b)**：假设 `[Fact (Nat.card 𝓀_F = p)]` 或直接给 `ε : 𝓀_F ≃+* ZMod p`，与问题 1 合并成一个参数；文档里说明它等价于完全分歧。
4. **`CoefficientRing` 用极大理想还是 `span {C ϖ}`**。极大理想版本消灭 `ϖ hϖ`；代价是 `Truncation` 变成 `O ⧸ 𝔪^(r+1)`，`parameter`（ϖ 的像）只在证明里出现。**建议极大理想**。
5. **抽象层的群**：保留抽象 `Γ`（现状），还是直接取 `Γ = L ≃ₐ[K] L`？抽象层让 `CoefficientRing/` 与 `Liftability/Defs` 完全不依赖 FW，可独立上游/复用。**建议保留抽象 `Γ`**。
6. Prop 1.3 的 `FiniteLiftable` 子集版本是否需要一般 `S : Set Γ`，还是只做 `Finset`/具体两元？**建议 `Set Γ`**（陈述最接近论文"any prescribed collection"）。

---

## C. 全局设计决策（影响全库）

### C1. 替换 `subst` 的接口

现状 `LaurentSeries.subst (δ : R) (hδ : IsNilpotent δ) [(Ideal.span {δ}).IsMaximal] (G) (hG : IsAdmissible δ G)`：
- `[(Ideal.span {δ}).IsMaximal]` 对 `δ = 0` 不是 Mathlib 规范形（`⊥`），故 7 个 LaurentSeries 文件 + 14 处其他文件各复制一份 `local instance`；对 `δ = parameter π r` 则 48 处 `let := parameter_isMaximal π hπ r hr`。
- `hδ`、`hG` 是显式证明参数，于是 `IsNilpotent.zero` 显式 61 次，而每个 `subst` 出现处都带一个 admissibility 证明项，进入 `CompletedLift.commute` 等字段的类型。
- `subst` 本身是 `Classical.choose (∃ F, 连续 ∧ F X = G ∧ 链式法则)`：唯一性靠 `subst_unique`，所有性质靠 `choose_spec` 读出。

**建议**：
1. 把"系数环"抽象为 `[CommRing R] [IsLocalRing R] [IsNilpotent (IsLocalRing.maximalIdeal R)]`（或 Mathlib 的 `IsArtinianRing`+local），`IsAdmissible G : Prop := 0 < orderTop (G mod 𝔪)`；field 情形 `𝔪 = ⊥` 自动满足，`Truncation` 情形给一个全局 `instance`。`δ`、`hδ` 从签名消失。
2. `subst G : LaurentSeries R →ₐ[R] LaurentSeries R` 对**所有** `G` 定义（非 admissible 时取 junk，例如 `AlgHom.id`），性质定理带 `(hG : IsAdmissible G)`。这样 `P ∘ F g` 可以写成 `subst (F g) P`，`Lift` 的字段类型里不再出现证明项；`commute_iff` 之类的迁移定理也不用逐字段对齐证明项。
3. 定义仍可经 `Classical.choose`，但 `IsAdmissible` 下的"连续 + 送 X 到 G"刻画作为 `subst_unique` 保留。给 `PowerSeries` 情形的 `powerSeriesSubstEquiv` 同样去掉证明参数（用 `IsUnit (coeff 1)` 作为性质而非参数：定义对所有 `P` 用 `substInvOfIsUnit` 的 junk 值）。
4. 记号：给 `subst G f` 一个 scoped 记号 `f ∘ₛ G`（或 `f.comp G`），论文的 `Q ∘ G` 直接可读。

### C2. `derivativeLevel` / `normalizedDerivative` 只依赖 `P`

现状 `derivativeLevel π hπ p e u hu hpe P hP := Classical.choose (exists_unique_derivative_layer …)`：七个前置参数，其中 `(e u hu hpe)` 是 `p = ϖ^e u` 的一个具体分解，不同分解给出语法上不同的 `h_P`（于是需要 `normalizedDerivative_eq_layerResidue` 做桥）。

**建议**：`derivativeLevel P := sInf {s | P' ∉ 𝔪^(s+1)}`（`Nat.find` 版），`normalizedDerivative P := Λ_s⁻¹ P'`；`1 ≤ s(P) ≤ e` 与 Lemma 2.4 (3) 作为定理，`e := absoluteRamificationIdx`（FTE 已有 `absoluteRamificationIdx p K := (addVal 𝒪[K] p).toNat`）。`c = p/ϖ^e` 的单位用 `IsDiscreteValuationRing` 的 `exists_unit_mul_pow`-型引理在证明内取。

### C3. 标准假设束与记号（对齐 FW/FTE 的 CLAUDE.md）

- 全库 `open scoped NormedField Valued NNReal FontaineWintenberger FalseTateExtension`；`𝒪[K]`、`𝓀[K]`、`ℚ_[p]`、`ℤ_[p]`；禁止 `OK/R/κK/O_F/O_0/O_E` 等局部记号。
- 一般 `K`：`[NontriviallyNormedField K] [IsPerfectResidueLocalField K]`，`p := residueChar K`（跟 FW）；p 进层：`(p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)]`，`K = ℚ_[p]`，`π : 𝒪[ℚ_[p]]` 显式 + `[Fact (Irreducible π)]`（跟 FTE）；边界用 `residueChar_padic`。
- `[IsAPF K L] [Fact (¬ Module.Finite K L)] [IsGalois K L] [IsResidueTrivial K L]` 全是 instance；为 `falseTateExtension p π` 补 `instance : Fact (¬ Module.Finite ℚ_[p] (falseTateExtension p π))`（FTE 只有 theorem）。
- 坐标级数的"切于恒等"、"无限阶"、"分歧数"各给定义：`IsTangent f := constantCoeff f = 0 ∧ coeff 1 f = 1`，`ramificationNumber f n : ℤ := (f^{∘ p^n} − T).order − 1`（论文 `d_n`），`HasInfiniteOrder f`。这三个表达式现在以 5–8 行的原文形式在 ≥ 15 条陈述中重复。
- `local notation` 政策与 FTE 相同：只在 section 内、只用于证明体，不进公开陈述。

### C4. Laurent 级数的拓扑

现状：手写 `orderTopology R : TopologicalSpace (LaurentSeries R)`（`RingSubgroupsBasis`，对任意交换环 `R`），**不是 instance**，每个用到的证明开头 `let := orderTopology R; have := orderTopology_t2Space`（≈ 25 处），所有连续性陈述写成 `@Continuous _ _ (orderTopology R) (orderTopology S) f`。原因是 Mathlib 对域 `K` 已有 `Valued (LaurentSeries K) ℤᵐ⁰` 诱导的拓扑，直接做 instance 会在域上产生 diamond。

选项：(a) 保持非 instance（现状，啰嗦）；(b) 做成 `scoped instance`，并证明对域 `K` 它与 `Valued` 拓扑**相等**（命题相等即可，只在两个 section 交界处 `rw`）；(c) 对 nilpotent 系数环的需要重新审视——`CoefficientRing/` 里实际只用它证 `subst` 的连续性与唯一性，而唯一性可以改为代数证明（`continuous_algHom_ext_X` 的 truncation 稠密论证换成"在 `R[T, T⁻¹]` 上相等 + 连续"仍需拓扑）。**建议 (b)**，并把需要的"两拓扑相等"引理放 `Mathlib/` 层。

### C5. 去掉"系数搬运"层

`FieldOfNorms/Liftability.lean` 的 `sourceNormFieldCoordinate → normFieldCoordinate → bergerCoordinateFamily`（κL → κK → κE）三层，各自重复 6 条引理；`FiniteObstruction.lean` 又有一段把 `ZMod p` 上的 §4 结果经 `ε` 搬到 `ResidueField O` 上的 10 条引理（`coefficient_map_*`）。

**建议**：`CoordinateFamily.mapResidue (ε : κ ≃+* κ')` 一个定义 + 一条 `liftable_mapResidue_iff`；§4 的三个结果（4.1、4.2、4.3）从 `ZMod p` 推广到任意 `[Field κ] [Fintype κ] [CharP κ p]`（它们只用到 `κ` 有限、特征 `p`、`(p−1)`-次单位根的存在——`UnitRigidity` 对 `Fintype.card κ = q` 的一般情形同样成立），搬运层整体删除。需确认 `PowerSeries/PrincipalUnitPowers` 的 `padicBinomialSeries`（`binomialSeries ℤ_[p] c` 映到 `ZMod p`）推广到 `CharP κ p` 的 `κ` 没有障碍（系数经 `ZMod p → κ` 映射即可）。

---

## D. 目录结构（建议）

原则与 FW/FTE 相同：按数学分层，每层一个聚合文件，脚本检查分层 import 与覆盖；`Mathlib/` 上游候选零项目依赖；40 → 约 22 个文件。

```
FalseTateNonliftability/
  Mathlib/                      上游候选（Mathlib 命名空间，零项目 import）
    RingTheory/HahnSeries/Map.lean          HahnSeries.map 打包为 →+*；R((T))/(a) ≃ (R/a)((T))   ← LaurentSeries/PrincipalQuotient
    RingTheory/LaurentSeries/Derivative.lean coeff_derivative, derivative_single/C/mul/pow, 特征 p 的像与核  ← CharacteristicP + FrobeniusKernel + Derivative(非 eval 部分) + PrimitiveNormalization
    RingTheory/LaurentSeries/Topology.lean  任意环上的 T 进拓扑及与 Valued 拓扑的比较   ← OrderTopology（+ 散落在 Taylor/NormalForm 的 orderAddSubgroup 引理）
    RingTheory/PowerSeries/Compactness.lean CompactSpace (PowerSeries k) 对有限 k；单位集紧   ← PowerSeries/UnitCompactness
    RingTheory/AdicCompletion/Quotient.lean ker (evalₐ I r)、AdicCompletion I R ⧸ Î^r ≃ R ⧸ I^r   ← CoefficientRing/Quotient
    NumberTheory/Padics/Continuity.lean     PadicInt.continuous_toZMod、exists_tendsto_of_prime_mul_tendsto（FTE 已有同名文件，可直接上游到 FTE）
  LaurentSeries/                纯 Laurent 级数（任意系数环或域），论文 §2.1 的形式性质与 §3 的级数计算
    Substitution.lean           nilpotent 系数的求值族、subst、唯一性、链式法则、powerSeriesSubstEquiv、conj、iterate   ← NilpotentPower + PowerSeriesEval + Evaluation + EvaluationContinuity + TruncationDensity + Admissible + Substitution + CoefficientMap（eval 部分）
    Taylor.lean                 Lemma 3.2、Thm 3.1 的级数核心（h∘f − h 的 Taylor 展开）   ← Taylor + ValuationBound 的 LaurentSeries 部分 + NormalizedDerivative:64–154 的两条域上引理
    NormalForm.lean             Lemma 3.3、Thm 3.4、分歧数 d_n 的定义与增长   ← NormalForm + IterateGrowth
  PowerSeries/                  主单位群：p 进幂、刚性
    PrincipalUnits.lean         z^c (c ∈ ℤ_p)、阶公式、连续性   ← PrincipalUnitIntegerPowers + PrincipalUnitPowers
    UnitRigidity.lean           Lemma 4.2 的核心（(f/T)^m (U∘f) = U ⇒ m = 0）   ← UnitRigidity
  Differential/                 论文 §4
    ApproximateInvariants.lean  Lemma 4.2
    InvariantExactDifferential.lean  Lemma 4.1
    ExactDifferentialLimit.lean Prop 4.3
  CoefficientRing/              论文 §2.2、§3.1、§6 的"系数环"部分，对抽象 DVR O（不依赖 FW/FTE）
    Truncation.lean             A_K、R_r = (O/𝔪^{r+1})((T))、层 Λ_j   ← Quotient(项目部分) + Truncation + Graded + NormalizedDerivative:202–405
    Substitution.lean           A_K 与 R_r 上的 subst、合成、坐标共轭 H∘P∘H⁻¹   ← Substitution + CoordinateChange
    NormalizedDerivative.lean   s(P)、h_P、Lemma 2.4 (1)(2)(3)、Thm 3.1   ← NormalizedDerivative:407–1092 + ValuationBound(CR 部分)
    Obstruction.lean            §6 两种情形的抽象版：level e ⇒ 与 d_k → ∞ 矛盾；level < e ⇒ 与 p 进极限矛盾   ← TopLevelObstruction + FiniteObstruction
  Liftability/                  Definition 1.1、Prop 1.3 的形状、Prop 2.3
    Defs.lean                   CoordinateFamily、Lift、Liftable、FiniteLiftable、mapResidue   ← CoefficientRing/Liftability
    CoordinateChange.lean       Prop 2.3 抽象版（conj 不变性）   ← FieldOfNorms/CoordinateChange 前半
    FieldOfNorms.lean           FieldOfNorms.coordinateFamily（Lemma 2.2）、IsLiftable、isLiftable_iff_uniformizer   ← FieldOfNorms/Liftability + CoordinateChange 后半
  FalseTate/                    论文 §5–6，K = ℚ_p
    RamificationNumbers.lean    Prop 5.1：d_k 经 FW Transfer + FTE TauRamification；p 进极限   ← 旧 FTE NormFieldRamification/KummerRamification §PadicLimit 的重做
    TameGenerator.lean          δ 与 Lemma 5.3   ← 旧 FTE TameGenerator + NormFieldAction 后半
    Main.lean（或 TheoremA.lean）Prop 1.3、Theorem A   ← TheoremA + DerivativeLevel
FalseTateNonliftability.lean    每层一个聚合 import；模块文档列出 Def 1.1 / Prop 1.3 / Prop 2.3 / Thm A 对应的声明
```

分层规则（脚本检查）：`Mathlib < LaurentSeries < PowerSeries < Differential < CoefficientRing < Liftability < FalseTate`；`Mathlib`–`CoefficientRing` 五层**不得 import FW/FTE**（现状 `CoefficientRing/Truncation`、`NormalizedDerivative`、`FiniteObstruction` 都 import 了，仅为了最后的 `coefficientExtension_*` 包装段——这些包装段合并到 `FalseTate/` 或删除）。

现状的分层倒置必须消除：`LaurentSeries/NormalForm` import `CoefficientRing/NormalizedDerivative`（1188 行）只为两条域上的引理（`order_powerSeriesSubstEquiv`、`order_derivative_ofPowerSeries`），导致 `NormalForm`、`IterateGrowth`、`UnitRigidity`、整个 §4 链都压在 `CoefficientRing` 之上，任何 `CoefficientRing` 改动都重编 §3–§4。

关于 `CoefficientRing/LocalRing.lean` + `DiscreteValuation.lean`（320 行，"`A_K` 是局部环 / DVR"）：零下游。它对应论文 Def 1.1 里的一句话"which is a complete discrete valuation ring with uniformizer ϖ_F and residue field 𝔽_q((T))"。选项：(a) 删除；(b) 保留并作为 `CoefficientRing` 的 instance（`IsDiscreteValuationRing (CoefficientRing O)`），文档标注"Def 1.1 的陈述部分，证明中未用"。**建议 (b)**（但把 `Nat.find`/`∃`-链改写干净，`IsLocalRing` 做 instance）。

死代码：按 FTE 的做法（不设 Attic，直接删，git 保留）。候选：`DiscreteValuation` 的 ∃ 链、六段 `coefficientExtension_*` 包装、`ValuationBound:198–289` 的完备化/`O_F` 尾部、`PrincipalUnitIntegerPowers` 的 6 条 ℤ 指数引理、`PrincipalUnitPowers` 的 25 条未用引理、`exists_laurent_normalForm`、`subst_comp`、`nilpotentLaurentEval_X_inv/_single_neg/…`、`derivative_units_inv/_zpow`、`TruncationDensity` 的两条 eval 引理等。估计 −1 500 行。

---

## E. 命名

- 通用：Mathlib 约定；去掉所有 `actual/original/genuine/canonical/…`；定理名 `exists_actual_substitution` → `exists_subst`；`isAdmissible_iff_actualResidue` → `isAdmissible_iff_residue`；section 名 `ActualCoordinates`/`OriginalNormCoordinates`/`IntrinsicLiftability` 等改为数学名。
- 核心对象：

| 现名 | 新名 |
|---|---|
| `PrincipalCompletion π` | `CoefficientRing O`（A_K） |
| `Truncation π r` | `Truncation O r`（`O ⧸ 𝔪^(r+1)`）或 Mathlib 的 `O ⧸ 𝔪^(r+1)` 直接写 |
| `parameter π r`、`residue π hπ r hr`、`factor π hsr` | `Truncation.mk`/`residue`/`factor`（去证明参数） |
| `layerResidue π hπ r j hjr X hX` | `layer j X`（Λ_j⁻¹；对 `X ∉ 𝔪^j` 取 junk） |
| `completedSubst π hπ G hG J`、`truncatedSubst …` | `subst G J` 统一一个名字（A_K 与 R_r 上各一个 instance of 同一接口，见 C1） |
| `coordinateConjugate`、`completedCoordinateConjugate`、`powerSeriesConjugate` | `conj H P`（`H ∘ P ∘ H⁻¹`） |
| `powerSeriesIterate f n` | `iterate f n`（`f^{∘n}`） |
| `powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hl` | `substEquiv f` |
| `substitutionDifference` | `substSubOne`（`σ − 1`） |
| `derivativeLevel π hπ p e u hu hpe P hP` / `normalizedDerivative …` | `derivativeLevel P` / `normalizedDerivative P` |
| `CompletedLift`、`FiniteLift`、`Liftable`、`FiniteLiftable` | `CoordinateFamily.Lift`、`.FiniteLift`、`.Liftable`、`.FiniteLiftable` |
| `bergerCoordinateFamily`、`normFieldCoordinate`、`sourceNormFieldCoordinate` | `FieldOfNorms.coordinateFamily`（一个） |
| `BergerLiftable K L E` | `IsLiftable K L F ε`（名字跟论文 "F-liftable"；Berger 在 docstring 里引用） |
| `falseTate_not_bergerLiftable` | `not_isLiftable_falseTate`（Theorem A） |
| `falseTate_finite_obstruction` | `not_finiteLiftable_falseTate`（Prop 1.3） |
| `not_commuting_finite_lifts_of_numerical_ramification`（24 个前提 → `False`） | 拆成 `derivativeLevel_lt_of_ramification_tendsto_atTop`（§6 情形 1）与 `not_lt_absoluteRamificationIdx_of_…`（情形 2），前提打包进 structure（见 C3） |
| `kummerRamificationLimit p` | `kummerRamificationLimit p`（保留，`(p−1)/(p+1) ∈ ℤ_p`） |
| `tameGenerator` | `tameGenerator`，记号 `δ` |
| `principalUnitPow z hz c` | `principalUnitPow z c`（`z ↦ z^c`，非主单位时 junk） |
| `padicBinomialSeries` | `binomialSeries`（放 `PowerSeries` 命名空间，对 `CharP κ p`） |

---

## F. 性能

实测热点只有一处，但结构性问题会在重构后放大，先列根因：

| 现象 | 根因 | 修法 |
|---|---|---|
| `TheoremA` 31–58 s | 30 条声明每条带 `hp₂ hπ htotal u hu` 五个参数 + 陈述内 `letI := normLimitField …`（每条重新 elaborate `Field (NormLimit …)`）；`@BergerLiftable` 的 14 个 `_` 让 unifier 反复综合；`Subsingleton.elim` 证两个 `ZMod p →+* κF` 相等 | 依赖升级后 `letI` 全部消失；坐标搬运层删除后此文件剩 Prop 1.3 + Thm A 两条，预计 < 5 s |
| `FieldOfNorms/{Liftability, CoordinateChange}` 15 s | 同上（`letI := normLimitField` 21 处） | 同上 |
| 基础文件改动 → 全库重编 | 分层倒置（§D）；`Derivative.lean` 用拓扑证 Leibniz 法则，把整条求值链压在导数之下 | Leibniz 改为系数证明（两行 `HahnSeries.coeff_mul`），`Derivative` 只依赖 Mathlib |
| `def … := by …` 的定义体（`truncatedSubst`、`coordinateConjugate`、`completedPowerSeriesSubstEquiv`、`powerSeriesSubstEquiv`、`residueTeichmuller` 式写法） | 每次 unfold 重跑 tactic，`rfl` 证明靠运气 | term-mode 定义 |
| `set_option backward.isDefEq.respectTransparency false`（`PowerSeriesEval:39`） | `SummableFamily.mul` 的 defeq 滥用 | 随 `Substitution` 合并时用 `HahnSeries.SummableFamily.powers`（Mathlib 已有，`0 < orderTop`）重写 `Y = 0` 情形，一般情形只做一次 |
| `nlinarith` ×12（全是线性目标）、`convert` ×8、三个 ≥ 65 行的 `simpa only [15+ lemmas]` | — | `omega`/`linarith`；拆引理 |
| `local instance … IsMaximal` ×21、`let := parameter_isMaximal` ×48 | C1 | C1 |

目标线（与 FTE 相同）：**单文件 < 30 s，全量（本项目）< 2 min CPU，`set_option` 归零**；每阶段末把 `lake build` 的各模块耗时追加到 `docs/BUILD_TIMES.md`（基线即本文 §0 数据，注明五个伪影）。

---

## G. 文档与工程

1. **版权头**（全部 40 文件）、`LICENSE`（Apache 2.0，从 FW 复制）、`README.md`（四个目标 ↔ 声明名的表；布局；构建）、`CLAUDE.md`（分层规则、标准假设束 §C3、记号政策、性能红线、`local notation` 规则——可从 FTE 的拷过来改）、`docs/REFACTOR_PLAN.md`（本文）、`docs/BUILD_TIMES.md`、`docs/MATHLIB_REUSE.md`。
2. **`.gitignore`** 加 `*.pdf`；README 注明所需文献（FalseTateLift.pdf 不分发）。
3. **模块文档**用 Mathlib 模板：`# 标题` / 一段数学陈述 / `## Main definitions` / `## Main results` / `## References`（Yuan, *Non-liftability …*, Lemma n.m；Berger 2014 Def；Wintenberger 3.3.2；Viviani 6.10）。**删除**全部 40 处 `nl:*`/`ft:*` 标签与"blueprint"字样；16 处 "Yuan, Lemma x.y" 改为正确编号（现状 2.3→2.4、4.1→4.2、4.2→4.3、"§6 (6.1)"→Lemma 4.1）。
4. **声明 docstring**：陈述数学（"`h_P ∘ f = (f')^{p−1} h_P` for every `G` commuting with `P`"），不写证明策略，不写"no … is assumed / … is a producer, not a hypothesis / without identifying scalar structures"这类话。约 880 处填充词归零（脚本 + 人工重写）。
5. **CI**：`lean_action_ci.yml` 现在只 build；加 `scripts/check_layers.py`（从 FTE 复制）与 `lake build` 零警告检查。确认 `actions/checkout@v5`/`lean-action@v1` 版本。
6. **fw-workspace**：`~/fw-workspace/projects/FalseTateNonliftability` 是同一代码的旧拷贝（带 `blueprint/`、`hgraph/`，钉旧依赖）。重构后它将过时；建议作者决定是否删除或改为 symlink，以免 `horizon` 工具继续读旧版。

---

## H. FontaineWintenberger `Attic/` 的评估（结论：**本项目一个都不需要**）

逐文件核对了 8 个文件的全部声明在本项目的引用（0 处）及其数学内容：

| Attic 文件 | 内容 | 本项目是否需要 |
|---|---|---|
| `AbsoluteGaloisGroupStatements` | 五个目标用 `Field.absoluteGaloisGroup` 的转写 | 否（本项目只用 `L ≃ₐ[K] L`） |
| `EmbeddingRestrictionBounds` | 有限基域上限制映射的 APF 界 | 否 |
| `FiniteUniformizer` | "任一 uniformizer 计算有限惯性分歧数"（Serre IV §1 的 `i_G(σ) = v(σπ − π)`） | 否——本项目需要的是 norm-field 版本，FW 正文 `Transfer.lean` 已有 `FieldOfNorms.ramificationNumber_eq_uniformizer`，FTE 正文已有 `addVal_tauPowRestrict_uniformizer` |
| `KrasnerValuation` | `Valued` 表述下的 Krasner 搬运 | 否 |
| `LowerFixedQuotient` | 下分歧群商的 Herbrand 性质 | 否 |
| `RelativeStages` | `RelFieldOfNorms` 的相对/环境搬运 | 否 |
| `ResidueLayerComposite` | 第二个 `𝓀[X_K(L)] ≃+* 𝓀_L` 方向（经深层坐标归约） | 否——`FieldOfNorms.laurentEquiv` 已固定使用正文的 `residueEquiv`；本项目只经 `laurentEquiv_C` 接触剩余域等同 |
| `UniversalDiscriminant` | 判别式的通用多项式 | 否 |

FTE 方案 A1 里"重做 FalseTateNonliftability 时再评估 `ResidueLayerComposite`、`RelativeStages`"的保留意见可以关闭。

---

## I. 执行顺序（每阶段一个分支，阶段末零错误零警告、全量 build、记录耗时后合并）

| 阶段 | 内容 | 预计 |
|---|---|---|
| U0 | 工程底座：版权头、LICENSE、README 占位、CLAUDE.md、`.gitignore` pdf、`docs/` 三个文件、CI 加脚本；修 85 处长行使 lakefile 的 linter 零警告 | 半天 |
| U1 | **依赖升级到目标版本（最小改动）**：改 manifest；按 §A2 表机械改名、删 `letI := normLimitField …`、`Fact (IsAPF)` → instance；在本项目重建 A2 表的四块（`RamificationNumbers`、`TameGenerator`、`not_finiteDimensional` instance、`kummerRamificationLimit`）。Theorem A 重新编译通过即合并。**不改设计** | 2–3 天，主要是 `RamificationNumbers`（FW Transfer ↔ FTE ramificationOrder 的对接） |
| R1 | C1：`subst` 接口（`IsLocalRing` + nilpotent 极大理想、Prop 式 admissibility、无证明参数）；C4 拓扑 scoped instance；Leibniz 改系数证明；消除分层倒置（两条域上引理下移） | 中 |
| R2 | C2 + B：`CoefficientRing O` 改极大理想完备化，`r+1` 索引，`derivativeLevel P`；`CoordinateFamily`/`Lift`/`Liftable`/`FiniteLiftable`；Prop 2.3 抽象版重写 | 高（`CoefficientRing/` 全部签名变化） |
| R3 | C5：§4 三个结果推广到有限 `κ`，删搬运层；`FieldOfNorms.coordinateFamily`、`IsLiftable`、`isLiftable_iff_uniformizer` | 中 |
| R4 | D：目录重组 + 死代码删除 + E 命名（脚本） | 低（机械） |
| R5 | F 剩余性能项、`set_option` 归零、`nlinarith`/`convert` 清理 | 低 |
| R6 | G：docstring 重写、References、README 目标表、BUILD_TIMES 终表 | 低 |

U1 与 R1–R6 之间可以合并一次，确保 GitHub 上的本项目先有一个能在新上游下编译的版本。

---

## 附录：论文结果 ↔ 现有声明 ↔ 问题（用于逐条讨论）

| 论文 | 现有声明 | 评价 |
|---|---|---|
| Def 1.1 | `CoefficientRing.Liftable`、`BergerLiftable` | 见 §B |
| Prop 1.3 | `falseTate_finite_obstruction`（`let` 进陈述，三元但形状丑） | 见 §B2 |
| Lemma 2.1 | `LaurentSeries.subst`/`subst_comp`/`derivative_subst`/`exists_unique_powerSeries_subst_inverse`，A_K 版 `completedSubst`/`completedSubst_comp`/`completedPowerSeriesSubstEquiv` | 内容齐；接口见 C1；A_K 版 `completedSubst_comp` 零下游 |
| Lemma 2.2 | `sourceNormFieldCoordinate_*`（一般 L/K）、旧 FTE `falseTatePowerSeriesCoordinate_*`（ℚ_p） | 两份；留一般版 |
| Prop 2.3 | `liftable_coordinateChange_iff`、`bergerLiftable_iff_uniformizer` 等 | 内容齐，陈述带 `Fact.out` 记号 |
| Lemma 2.4 (1)(2)(3) | `normalizedDerivative_commuting_substitution`、`derivativeLevel_coordinateConjugate` + `normalizedDerivative_coordinateConjugate` + `order_normalizedDerivative_coordinateConjugate`、`normalizedDerivative_eq_derivative_of_lt` + `normalizedDerivative_eq_single_add_derivative_of_eq` + `derivative_normalizedDerivative_ne_zero_and_order_le_of_eq` | 忠实；(2) 只对 `H ∈ T(O/ϖ^{e+1})⟦T⟧` 线性系数可逆证明（与论文相同）；`s(P)` 的定义见 C2 |
| Thm 3.1 | `order_le_of_subst_eq_derivative_pow_mul`（级数核心）+ `order_normalizedDerivative_le_of_top` | 忠实，核心引理分离得好 |
| Lemma 3.2 | `orderTop_powerSeriesConjugate_sub_variable`、`subst_sub_mem_orderAddSubgroup`、`subst_sub_leadingTerm_mem` | 忠实 |
| Lemma 3.3 | `resonant_iterate_orderTop` | 忠实 |
| Thm 3.4 | `exists_powerSeries_normalForm`（99 行；`∃ (w) (_hw) (hwlinear) (α), α ≠ 0 ∧ …`） | 忠实，陈述形状待改 |
| Lemma 4.1 | `exists_exact_invariant_of_weighted_identities`（`ZMod p`） | 忠实，推广到有限 κ |
| Lemma 4.2 | `padic_limit_order_eq_zero_of_approximate_invariance` + `PowerSeries/UnitRigidity` | 忠实 |
| Prop 4.3 | `padic_ramification_limit_eq_of_invariant_exact_differential`（`let E := …; let x := …` 进陈述） | 忠实，陈述形状待改 |
| Prop 5.1 | 旧 FTE `NormFieldRamification` + `KummerRamification §PadicLimit`（已被上游删除） | **须重做**（§A2） |
| Lemma 5.3 | 旧 FTE `NormFieldAction` 后半（已被上游删除） | **须重做**（§A2） |
| §6 情形 1 / 情形 2 | `derivativeLevel_lt_of_iterate_growth` / `not_commuting_finite_lifts_of_numerical_ramification` | 忠实；后者 24 个前提待打包 |
| Thm A | `falseTate_not_bergerLiftable` | 见 §B |
