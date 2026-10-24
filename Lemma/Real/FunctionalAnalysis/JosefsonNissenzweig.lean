import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.FunctionalAnalysis.JosefsonNissenzweig
open MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted


namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rclike_of_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rclike_of_real
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  (hInf : ¬ FiniteDimensional 𝕜 E)
  (hreal : ¬ FiniteDimensional ℝ E →
    ∃ (φ : ℕ → StrongDual ℝ E), (∀ n, ‖φ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : ℝ))) :
  ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  have hInfReal : ¬ FiniteDimensional ℝ E := by
    intro h
    apply hInf
    let _ : FiniteDimensional ℝ E := h
    exact Module.Finite.of_restrictScalars_finite ℝ 𝕜 E
  obtain ⟨φ, hφnorm, hφ⟩ := hreal hInfReal
  refine ⟨fun n => (φ n).extendRCLike, ?_, ?_⟩
  · intro n
    exact StrongDual.norm_extendRCLike (φ n) |>.trans (hφnorm n)
  · intro x
    have hx : Filter.Tendsto (RCLike.ofReal ∘ fun n => (φ n) x) Filter.atTop
      (nhds (0 : 𝕜)) := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto 0).comp (hφ x)
    have hIx : Filter.Tendsto
      (RCLike.ofReal ∘ fun n => (φ n) ((RCLike.I : 𝕜) • x)) Filter.atTop
      (nhds (0 : 𝕜)) := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto 0).comp (hφ ((RCLike.I : 𝕜) • x))
    change Filter.Tendsto (fun n => RCLike.ofReal ((φ n) x) -
      (RCLike.I : 𝕜) * RCLike.ofReal ((φ n) ((RCLike.I : 𝕜) • x))) Filter.atTop (nhds 0)
    simpa only [Function.comp_apply, mul_zero, sub_zero] using
      hx.sub (tendsto_const_nhds.mul hIx)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_dual_infinite_dimensional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_dual_infinite_dimensional
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (hInf : ¬ FiniteDimensional 𝕜 E) :
  ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 E) := by
  intro hDual
  apply hInf
  let _ : FiniteDimensional 𝕜 (StrongDual 𝕜 E) := hDual
  let _ : FiniteDimensional 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM 𝕜)
      ContinuousLinearMap.coe_injective
  exact FiniteDimensional.of_injective (K := 𝕜) (V := E)
    (V₂ := StrongDual 𝕜 (StrongDual 𝕜 E))
    (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).injective

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_exists_separated_dual_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_exists_separated_dual_sequence
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (hInf : ¬ FiniteDimensional 𝕜 E) :
  ∃ (R : ℝ) (φ : ℕ → StrongDual 𝕜 E), 1 < R ∧
    (∀ n, ‖φ n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖φ m - φ n‖ :=
exists_seq_norm_le_one_le_norm_sub (jn_dual_infinite_dimensional hInf)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_of_pointwise_cauchy_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_of_pointwise_cauchy_subsequence
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (φ : ℕ → StrongDual 𝕜 E)
  (hsep : Pairwise fun m n => 1 ≤ ‖φ m - φ n‖)
  (u : ℕ → ℕ) (hu : StrictMono u)
  (hcauchy : ∀ x : E, CauchySeq (fun n => (φ (u n)) x)) :
  ∃ (ψ : ℕ → StrongDual 𝕜 E), (∀ n, ‖ψ n‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let d : ℕ → StrongDual 𝕜 E := fun n => φ (u (2 * n)) - φ (u (2 * n + 1))
  have hd : ∀ n, 1 ≤ ‖d n‖ := by
    intro n
    apply hsep
    exact hu.injective.ne (by omega)
  let ψ : ℕ → StrongDual 𝕜 E := fun n => (((‖d n‖⁻¹ : ℝ) : 𝕜) • d n)
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    have hpos : 0 < ‖d n‖ := lt_of_lt_of_le zero_lt_one (hd n)
    simp only [ψ, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hpos)]
  · intro x
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hcauchy x)
    have heven : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun a ha => ?_⟩
      omega
    have hodd : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun a ha => ?_⟩
      omega
    have hd0 : Filter.Tendsto (fun n => (d n) x) Filter.atTop (nhds (0 : 𝕜)) := by
      simpa only [Function.comp_apply, d, sub_apply, sub_self] using
        (ha.comp heven).sub (ha.comp hodd)
    rw [Metric.tendsto_atTop] at hd0 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hd0 ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hcoef : ‖(((‖d n‖⁻¹ : ℝ) : 𝕜))‖ ≤ 1 := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hd n))).2 (hd n)
    rw [dist_zero_right]
    calc
      ‖(ψ n) x‖ = ‖(((‖d n‖⁻¹ : ℝ) : 𝕜))‖ * ‖(d n) x‖ := by
        simp only [ψ, smul_apply, norm_smul]
      _ ≤ 1 * ‖(d n) x‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ < ε := by simpa only [one_mul, dist_zero_right] using hN n hn

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_of_lower_bounded_pointwise_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_of_lower_bounded_pointwise_null
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (φ : ℕ → StrongDual 𝕜 E) (δ : ℝ) (hδ : 0 < δ)
  (hlower : ∀ n, δ ≤ ‖φ n‖)
  (hnull : ∀ x : E,
    Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜))) :
  ∃ (ψ : ℕ → StrongDual 𝕜 E), (∀ n, ‖ψ n‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let ψ : ℕ → StrongDual 𝕜 E := fun n => (((‖φ n‖⁻¹ : ℝ) : 𝕜) • φ n)
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    have hpos : 0 < ‖φ n‖ := hδ.trans_le (hlower n)
    simp only [ψ, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hpos)]
  · intro x
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero_norm (a := fun n => δ⁻¹ * ‖(φ n) x‖)
    · intro n
      have hpos : 0 < ‖φ n‖ := hδ.trans_le (hlower n)
      have hcoef : ‖φ n‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hpos hδ).mpr (hlower n)
      simp only [ψ, smul_apply, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs,
        abs_mul, abs_inv, abs_norm]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((φ n) x))
    · simpa only [norm_zero, mul_zero] using (hnull x).norm.const_mul δ⁻¹

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_wholeGroupIndex_nested](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_wholeGroupIndex_nested
  {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (u : ℕ → ℕ)
  (n i : ℕ) (hi : i < p) :
  jnWholeGroupIndex (p * q) u (p * n + i) =
    p * (q * u (n / q) + n % q) + i := by
  have hrem : p * (n % q) + i < p * q := by
    have hnmod : n % q < q := Nat.mod_lt n hq
    have hleft : p * (n % q) + i < p * (n % q + 1) := by
      rw [Nat.mul_succ]
      omega
    have hright : p * (n % q + 1) ≤ p * q :=
      Nat.mul_le_mul_left p hnmod
    exact hleft.trans_le hright
  have hrepr : p * (n % q) + i + (p * q) * (n / q) = p * n + i := by
    have hn := Nat.mod_add_div n q
    calc
      p * (n % q) + i + (p * q) * (n / q) =
        p * (n % q + q * (n / q)) + i := by ring
      _ = p * n + i := by rw [hn]
  have hdivmod := (Nat.div_mod_unique (Nat.mul_pos hp hq)).2 ⟨hrepr, hrem⟩
  unfold jnWholeGroupIndex
  rw [hdivmod.1, hdivmod.2]
  ring

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_shift
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (f : JnBoundedSeq) (d : ℕ) : L f = L (jnShift d f) := by
  induction d with
  | zero =>
    congr 1
  | succ d ih =>
    rw [ih]
    apply hshift
    intro n
    simp only [jn_shift_apply]
    congr 1
    omega

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacher_shift_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacher_shift_self (k n : ℕ) :
  jnRademacher k (n + 2 ^ k) = -jnRademacher k n := by
  simp only [jn_rademacher_apply]
  rw [Nat.add_div_right n (by positivity : 0 < 2 ^ k)]
  rw [pow_succ]
  ring

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacher_shift_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacher_shift_of_lt {i k : ℕ} (hik : i < k) (n : ℕ) :
  jnRademacher i (n + 2 ^ k) = jnRademacher i n := by
  have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_of_le hik.le]
  have heven : Even (2 ^ (k - i)) :=
    Nat.even_pow.mpr ⟨even_two, Nat.sub_ne_zero_of_lt hik⟩
  simp only [jn_rademacher_apply, hpow]
  rw [Nat.add_mul_div_left n (2 ^ (k - i)) (by positivity : 0 < 2 ^ i)]
  rw [pow_add, heven.neg_one_pow, mul_one]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacher_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacher_period (k m i : ℕ) :
  jnRademacher k (2 ^ (k + 1) * m + i) = jnRademacher k i := by
  have hindex : 2 ^ (k + 1) * m + i = i + 2 ^ k * (2 * m) := by
    rw [pow_succ]
    ring
  rw [hindex]
  simp only [jn_rademacher_apply]
  rw [Nat.add_mul_div_left i (2 * m) (by positivity : 0 < 2 ^ k), pow_add]
  have heven : Even (2 * m) := even_two_mul m
  rw [heven.neg_one_pow, mul_one]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_blockApply_rademacherBlocking](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_blockApply_rademacherBlocking
  {E : Type*} [AddCommMonoid E] [Module ℝ E]
  (k : ℕ) (x : ℕ → E) (n : ℕ) :
  jnBlockApply (jnRademacherBlocking k) x n =
    ∑ i ∈ Finset.range (2 ^ (k + 1)),
      ((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i) •
        x (2 ^ (k + 1) * n + i) := by
  change Finsupp.linearCombination ℝ x
    (∑ i ∈ Finset.range (2 ^ (k + 1)),
      Finsupp.single (2 ^ (k + 1) * n + i)
        ((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_blockApply_rademacherBlocking_wholeGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_blockApply_rademacherBlocking_wholeGroup
  {E : Type*} [AddCommMonoid E] [Module ℝ E]
  {k j : ℕ} (hkj : k ≤ j) (u : ℕ → ℕ) (hu : StrictMono u)
  (x : ℕ → E) (n : ℕ) :
  jnBlockApply (jnRademacherBlocking k)
    (jnBlockApply (jnWholeGroupBlocking (2 ^ (j + 1)) (by positivity) u hu) x) n =
    jnBlockApply (jnRademacherBlocking k) x
      (jnWholeGroupIndex (2 ^ (j - k)) u n) := by
  have hpow : 2 ^ (j + 1) = 2 ^ (k + 1) * 2 ^ (j - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [jn_blockApply_rademacherBlocking, jn_blockApply_rademacherBlocking]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jn_blockApply_wholeGroup]
  congr 2
  rw [hpow]
  exact jn_wholeGroupIndex_nested (by positivity) (by positivity) u n i
    (Finset.mem_range.mp hi)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_rademacher_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_rademacher_orthogonal
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (i j : ℕ) : L (jnRademacher i * jnRademacher j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [← hone]
    apply congrArg L
    ext n
    simp only [BoundedContinuousFunction.mul_apply, jn_rademacher_apply,
      BoundedContinuousFunction.const_apply]
    have : (-1 : ℝ) ^ (n / 2 ^ i) = 1 ∨ (-1 : ℝ) ^ (n / 2 ^ i) = -1 := by
      exact neg_one_pow_eq_or ℝ _
    obtain h | h <;> rw [h] <;> norm_num := this
  · simp only [hij, ite_false]
    have hlt : ∀ {a b : ℕ}, a < b → L (jnRademacher a * jnRademacher b) = 0 := by
      intro a b hab
      have hs := jn_banach_shift L hshift (jnRademacher a * jnRademacher b) (2 ^ b)
      have heq : jnShift (2 ^ b) (jnRademacher a * jnRademacher b) =
        -(jnRademacher a * jnRademacher b) := by
        ext n
        simp only [jn_shift_apply, BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.neg_apply]
        rw [jn_rademacher_shift_of_lt hab, jn_rademacher_shift_self]
        ring
      rw [heq, map_neg] at hs
      linarith
    obtain hijlt | hjilt := Nat.lt_or_gt_of_ne hij
    · exact hlt hijlt
    · rw [mul_comm]
      exact hlt hjilt

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_const
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (a : ℝ) : L (BoundedContinuousFunction.const ℕ a) = a := by
  have hconst : BoundedContinuousFunction.const ℕ a =
    a • BoundedContinuousFunction.const ℕ (1 : ℝ) := by
    ext n
    simp
  rw [hconst, map_smul, hone, smul_eq_mul, mul_one]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_blockPrimitive_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_blockPrimitive_coboundary (p : ℕ) (hp : 0 < p)
  (f : JnBoundedSeq) :
  jnShift 1 (jnBlockPrimitive p hp f) - jnBlockPrimitive p hp f =
    f - jnBlockMean p hp f := by
  ext n
  simp only [BoundedContinuousFunction.sub_apply, jn_shift_apply,
    jn_blockPrimitive_apply]
  rw [show n + 1 = n.succ from rfl, jnPartialSum]
  rw [BoundedContinuousFunction.sub_apply]
  ring

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_blockMean](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_blockMean
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq) :
  L f = L (jnBlockMean p hp f) := by
  let g := jnBlockPrimitive p hp f
  have hs : L g = L (jnShift 1 g) := by
    apply hshift
    intro n
    rfl
  have hc := congrArg L (jn_blockPrimitive_coboundary p hp f)
  simp only [map_sub] at hc
  linarith

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_of_blockMeans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_of_blockMeans
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  {δ : ℝ} (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq)
  (hmean : ∀ n, δ ≤ jnBlockMean p hp f n) :
  δ ≤ L f := by
  let c : JnBoundedSeq := BoundedContinuousFunction.const ℕ δ
  have hnonneg : ∀ n, 0 ≤ (jnBlockMean p hp f - c) n := by
    intro n
    simp only [BoundedContinuousFunction.sub_apply, sub_nonneg]
    exact hmean n
  have hL := hpos (jnBlockMean p hp f - c) hnonneg
  rw [map_sub, jn_banach_const L hone] at hL
  rw [jn_banach_blockMean L hshift p hp f]
  exact sub_nonneg.mp hL

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_of_positive_block_means](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_of_positive_block_means
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  {δ : ℝ} (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq)
  (hmean : ∀ n, 0 < n →
    δ ≤ (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * n + i)) :
  δ ≤ L f := by
  let g := jnShift p f
  have hg : ∀ n, δ ≤ jnBlockMean p hp g n := by
    intro n
    rw [jn_blockMean_apply]
    have hsum : ∑ i ∈ Finset.range p, g (p * (n / p) + i) =
      ∑ i ∈ Finset.range p, f (p * (n / p + 1) + i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [g, jn_shift_apply]
      congr 1
      ring
    rw [hsum]
    exact hmean (n / p + 1) (Nat.zero_lt_succ _)
  have hgf := jn_banach_of_blockMeans L hpos hone hshift p hp g hg
  rwa [← jn_banach_shift L hshift f p] at hgf

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_rademacher_bessel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_rademacher_bessel
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (f : JnBoundedSeq) (N : ℕ) :
  ∑ i ∈ Finset.range N, (L (jnRademacher i * f)) ^ 2 ≤ ‖f‖ ^ 2 := by
  let c : ℕ → ℝ := fun i => L (jnRademacher i * f)
  let b : JnBoundedSeq := ∑ i ∈ Finset.range N, c i • jnRademacher i
  have hfb : L (f * b) = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
    simp only [b, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [c]
    rw [mul_comm f, mul_comm (L (jnRademacher i * f))]
    exact (pow_two _).symm
  have hbb : L (b * b) = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
    calc
      L (b * b) = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        c i * c j * L (jnRademacher j * jnRademacher i) := by
        simp only [b, Finset.sum_mul, Finset.mul_sum, map_sum, map_smul,
          mul_smul_comm, smul_mul_assoc, smul_eq_mul]
        simp only [mul_assoc]
      _ = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · rw [jn_banach_rademacher_orthogonal L hone hshift i i]
          simp [pow_two]
        · intro j hj hji
          rw [jn_banach_rademacher_orthogonal L hone hshift j i]
          simp only [hji, ite_false, mul_zero]
        · exact fun hnot => (hnot hi).elim
  have hsq : 0 ≤ L ((f - b) * (f - b)) := by
    apply hpos
    intro n
    simp only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply]
    exact mul_self_nonneg _
  have hsum_le : ∑ i ∈ Finset.range N, (c i) ^ 2 ≤ L (f * f) := by
    have hexpand : L ((f - b) * (f - b)) =
      L (f * f) - 2 * L (f * b) + L (b * b) := by
      have heq : (f - b) * (f - b) = f * f - (2 : ℝ) • (f * b) + b * b := by
        ext n
        simp only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        ring
      rw [heq, map_add, map_sub, map_smul]
      simp only [smul_eq_mul]
    rw [hexpand, hfb, hbb] at hsq
    linarith
  have hff : L (f * f) ≤ ‖f‖ ^ 2 := by
    let q : JnBoundedSeq := BoundedContinuousFunction.const ℕ (‖f‖ ^ 2) - f * f
    have hq : 0 ≤ L q := by
      apply hpos
      intro n
      simp only [q, BoundedContinuousFunction.sub_apply,
        BoundedContinuousFunction.const_apply, BoundedContinuousFunction.mul_apply,
        sub_nonneg]
      have habs : |f n| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm n
      simpa only [pow_two, abs_mul_abs_self] using
        (sq_le_sq₀ (abs_nonneg (f n)) (norm_nonneg f)).mpr habs
    simp only [q, map_sub, jn_banach_const L hone] at hq
    linarith
  simpa only [c] using hsum_le.trans hff

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_banach_rademacher_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_banach_rademacher_tendsto_zero
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (f : JnBoundedSeq) :
  Filter.Tendsto (fun i => L (jnRademacher i * f)) Filter.atTop (nhds 0) := by
  let a : ℕ → ℝ := fun i => L (jnRademacher i * f)
  have hsquares : Summable (fun i => (a i) ^ 2) := by
    refine summable_of_sum_range_le (c := ‖f‖ ^ 2) (fun i => sq_nonneg (a i)) ?_
    intro N
    exact jn_banach_rademacher_bessel L hpos hone hshift f N
  have hsquare0 : Filter.Tendsto (fun i => (a i) ^ 2) Filter.atTop (nhds 0) :=
    hsquares.tendsto_atTop_zero
  have habs0 : Filter.Tendsto (fun i => |a i|) Filter.atTop (nhds 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp hsquare0 using 1
    · funext i
      simp only [Function.comp_apply, Real.sqrt_sq_eq_abs]
    · simp
  simpa only [a] using (tendsto_zero_iff_norm_tendsto_zero.mpr habs0)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacher_block_mean_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacher_block_mean_eval
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R)
  (k n : ℕ) (x : E) :
  ((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ *
    ∑ i ∈ Finset.range (2 ^ (k + 1)),
      (jnRademacher k * jnBoundedEval z R hz x) (2 ^ (k + 1) * n + i) =
    jnBlockApply (jnRademacherBlocking k) z n x := by
  rw [jn_blockApply_rademacherBlocking]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    BoundedContinuousFunction.mul_apply, jn_boundedEval_apply]
  simp_rw [jn_rademacher_period]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacherFunctional_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacherFunctional_tendsto_zero
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R) (x : E) :
  Filter.Tendsto (fun k => jnRademacherFunctional L z R hz k x)
    Filter.atTop (nhds 0) := by
  simpa only [jn_rademacherFunctional_apply] using
    jn_banach_rademacher_tendsto_zero L hpos hone hshift (jnBoundedEval z R hz x)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_of_rademacher_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_of_rademacher_lower_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : JnBoundedSeq →L[ℝ] ℝ)
  (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
  (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
  (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
  (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R)
  (δ : ℝ) (hδ : 0 < δ)
  (hlower : ∀ k, δ ≤ ‖jnRademacherFunctional L z R hz k‖) :
  ∃ (ψ : ℕ → StrongDual ℝ E), (∀ k, ‖ψ k‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun k => (ψ k) x) Filter.atTop (nhds (0 : ℝ)) := by
  let w : ℕ → StrongDual ℝ E := fun k => jnRademacherFunctional L z R hz k
  let ψ : ℕ → StrongDual ℝ E := fun k => ‖w k‖⁻¹ • w k
  refine ⟨ψ, ?_, ?_⟩
  · intro k
    have hwpos : 0 < ‖w k‖ := hδ.trans_le (hlower k)
    simp only [ψ, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (ne_of_gt hwpos)]
  · intro x
    have hw0 : Filter.Tendsto (fun k => (w k) x) Filter.atTop (nhds (0 : ℝ)) :=
      jn_rademacherFunctional_tendsto_zero L hpos hone hshift z R hz x
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero_norm (a := fun k => δ⁻¹ * ‖(w k) x‖)
    · intro k
      have hwpos : 0 < ‖w k‖ := hδ.trans_le (hlower k)
      have hcoef : ‖w k‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hwpos hδ).mpr (hlower k)
      simp only [ψ, smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), abs_abs]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((w k) x))
    · simpa only [norm_zero, mul_zero] using hw0.norm.const_mul δ⁻¹

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_l1Lower_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_l1Lower_norm
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : ℝ} {x : ℕ → E} (hx : JnL1Lower c x) (n : ℕ) :
  c ≤ ‖x n‖ := by
  simpa using hx (Finsupp.single n 1)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_block_preserves_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_block_preserves_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : ℝ} {x : ℕ → E} (hx : ∀ n, ‖x n‖ ≤ R) (b : JnBlocking) :
  ∀ n, ‖jnBlockApply b x n‖ ≤ R := by
  intro n
  rw [jnBlockApply, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ i ∈ (b.coeff n).support, b.coeff n i • x i‖ ≤
      ∑ i ∈ (b.coeff n).support, ‖b.coeff n i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ (b.coeff n).support, |b.coeff n i| * R := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
    _ = R := by
      rw [← Finset.sum_mul, ← Finsupp.sum, ← jnCoeffNorm, b.norm_one, one_mul]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_l1Lower_of_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_l1Lower_of_uniform
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {x : ℕ → E}
  (hx : MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted.HasUniformL1LowerBound
    (𝕜 := ℝ) x) :
  ∃ c : ℝ, 0 < c ∧ JnL1Lower c x := by
  obtain ⟨c, hc, hx⟩ := hx
  refine ⟨c, hc, fun a => ?_⟩
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Real.norm_eq_abs] using hx a

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_add_le_of_dvd_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_add_le_of_dvd_of_lt
  {p a b : ℕ} (hp : 0 < p) (ha : p ∣ a) (hb : p ∣ b) (hab : a < b) :
  a + p ≤ b := by
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨s, hs⟩ := hb
  rw [hs] at hab ⊢
  have hrs : r < s := (Nat.mul_lt_mul_left hp).mp hab
  rw [← Nat.mul_succ]
  exact Nat.mul_le_mul_left p hrs

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_log2_group_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_log2_group_const (k n i : ℕ) (hn : 0 < n)
  (hi : i < 2 ^ (k + 1)) :
  Nat.log2 (2 ^ (k + 1) * n + i) =
    Nat.log2 (2 ^ (k + 1) * n) := by
  let p := 2 ^ (k + 1)
  let a := p * n
  let q := Nat.log2 a
  have hp : 0 < p := by simp [p]
  have ha : a ≠ 0 := Nat.mul_ne_zero hp.ne' hn.ne'
  have hq : k + 1 ≤ q := by
    apply (Nat.le_log2 ha).2
    exact Nat.le_mul_of_pos_right p hn
  have hupper : a + p ≤ 2 ^ (q + 1) := by
    apply jn_add_le_of_dvd_of_lt hp
    · exact dvd_mul_right p n
    · exact Nat.pow_dvd_pow 2 (hq.trans (Nat.le_succ q))
    · exact Nat.lt_log2_self
  apply (Nat.log2_eq_iff (by positivity : a + i ≠ 0)).2
  constructor
  · exact (Nat.log2_self_le ha).trans (Nat.le_add_right a i)
  · exact (Nat.add_lt_add_left hi a).trans_le hupper

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_blockApply_stableDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_blockApply_stableDiagonal
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (n : ℕ) :
  jnBlockApply (jnStableDiagonalBlocking hz) z n =
    jnBlockApply (jnStableBlockingChain hz (Nat.log2 n)) z n := by
  rfl

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_rademacher_stableDiagonal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_rademacher_stableDiagonal_eq
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
  (k n : ℕ) (hn : 0 < n) :
  jnBlockApply (jnRademacherBlocking k)
    (jnBlockApply (jnStableDiagonalBlocking hz) z) n =
    jnBlockApply (jnRademacherBlocking k)
      (jnBlockApply
        (jnStableBlockingChain hz (Nat.log2 (2 ^ (k + 1) * n))) z) n := by
  rw [jn_blockApply_rademacherBlocking, jn_blockApply_rademacherBlocking]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jn_blockApply_stableDiagonal,
    jn_log2_group_const k n i hn (Finset.mem_range.mp hi)]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[jn_not_stable_small](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma jn_not_stable_small
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {δ : ℝ} {z : ℕ → StrongDual ℝ E} (h : ¬JnBlockStable δ z) :
  ∃ b : JnBlocking, ∀ x : E, ‖x‖ ≤ 1 →
    ∃ N, ∀ n, N ≤ n → ‖jnBlockApply b z n x‖ < δ := by
  unfold JnBlockStable at h
  push Not at h
  exact h

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

/--
[josefson_nissenzweig](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma josefson_nissenzweig_eq
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
-- given
  (hInf : ¬ FiniteDimensional 𝕜 E) :
-- imply
  ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted.josefson_nissenzweig hInf


-- created on 2026-10-20
-- updated on 2026-10-23
