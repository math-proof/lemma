import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.LSeries.AsymptoticContinuation
open Filter Asymptotics Topology


/--
[abelPartialSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma abelPartialSum_sub_const
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {n : ℕ} :
-- imply
  abelPartialSum (fun k => a k - ρ) n = abelPartialSum a n - n • ρ := by
-- proof
  simp only [abelPartialSum, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel]

/--
[isBigO_abelPartialSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma isBigO_abelPartialSum_sub_const
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  (fun n => abelPartialSum (fun k => a k - ρ) n) =O[atTop]
    fun n => ((n : ℝ) ^ σ : ℝ) := by
-- proof
  simpa only [abelPartialSum_sub_const] using hO

/--
[analyticAt_linearAsymptoticDirichletContinuation_of_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma analyticAt_linearAsymptoticDirichletContinuation_of_ne_one
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ))
  (hs : σ < s.re)
  (hs1 : s ≠ 1) :
-- imply
  AnalyticAt ℂ (linearAsymptoticDirichletContinuation a ρ) s := by
-- proof
  have hremO := isBigO_abelPartialSum_sub_const a ρ hO
  have hrem : AnalyticAt ℂ (abelContinuation (fun n => a n - ρ)) s :=
    (analyticOn_abelContinuation (fun n => a n - ρ) hremO).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs1)
  change AnalyticAt ℂ
    (fun z => ρ * riemannZeta z + abelContinuation (fun n => a n - ρ) z) s
  have hconst : AnalyticAt ℂ (fun _ : ℂ => ρ) s := analyticAt_const
  exact (hconst.mul hzeta).add hrem

/--
[analyticAt_linearAsymptoticNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma analyticAt_linearAsymptoticNumerator
  (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ}
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
    fun n => ((n : ℝ) ^ σ : ℝ)) :
  AnalyticAt ℂ (linearAsymptoticNumerator a ρ) 1 := by
  have hremO := isBigO_abelPartialSum_sub_const a ρ hO
  have h1mem : (1 : ℂ) ∈ {s : ℂ | σ < s.re} := by simpa using hσ1
  have hrem : AnalyticAt ℂ (abelContinuation (fun n => a n - ρ)) 1 :=
    (analyticOn_abelContinuation (fun n => a n - ρ) hremO).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1mem)
  have hzeta : AnalyticAt ℂ riemannZeta₁ 1 :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Eventually.of_forall fun x => differentiable_riemannZeta₁ x)
  change AnalyticAt ℂ
    (fun z => ρ * riemannZeta₁ z + (z - 1) * abelContinuation (fun n => a n - ρ) z) 1
  have hconst : AnalyticAt ℂ (fun _ : ℂ => ρ) 1 := analyticAt_const
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 :=
    analyticAt_id.sub analyticAt_const
  exact (hconst.mul hzeta).add (hsub.mul hrem)

/--
[linearAsymptoticNumerator_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma linearAsymptoticNumerator_one (a : ℕ → ℂ) (ρ : ℂ) :
  linearAsymptoticNumerator a ρ 1 = ρ := by
  unfold linearAsymptoticNumerator
  simp [riemannZeta₁_one]

/--
[linearAsymptoticDirichletContinuation_eq_inv_sub_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma linearAsymptoticDirichletContinuation_eq_inv_sub_mul
  {a : ℕ → ℂ}
  {ρ s : ℂ}
-- given
  (hs : s ≠ 1) :
-- imply
  linearAsymptoticDirichletContinuation a ρ s =
    (s - 1)⁻¹ *
    (ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s) := by
-- proof
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold linearAsymptoticDirichletContinuation
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp

/--
[linearAsymptoticDirichletContinuation_eventuallyEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma linearAsymptoticDirichletContinuation_eventuallyEq
  (a : ℕ → ℂ) (ρ : ℂ) :
  linearAsymptoticDirichletContinuation a ρ =ᶠ[𝓝[≠] (1 : ℂ)]
    fun s => (s - 1) ^ (-1 : ℤ) • linearAsymptoticNumerator a ρ s := by
  change ∀ᶠ s in 𝓝[≠] (1 : ℂ),
    linearAsymptoticDirichletContinuation a ρ s =
      (s - 1) ^ (-1 : ℤ) • linearAsymptoticNumerator a ρ s
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s ≠ 1 := by simpa using hs
  rw [linearAsymptoticDirichletContinuation_eq_inv_sub_mul a ρ hne]
  unfold linearAsymptoticNumerator
  rw [zpow_neg_one, smul_eq_mul]

/--
[meromorphicAt_linearAsymptoticDirichletContinuation_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma meromorphicAt_linearAsymptoticDirichletContinuation_one
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  MeromorphicAt (linearAsymptoticDirichletContinuation a ρ) 1 := by
-- proof
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  exact ⟨-1, linearAsymptoticNumerator a ρ,
    analyticAt_linearAsymptoticNumerator a ρ hσ1 hO,
    linearAsymptoticDirichletContinuation_eventuallyEq a ρ⟩

/--
[meromorphicOrderAt_linearAsymptoticDirichletContinuation_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma meromorphicOrderAt_linearAsymptoticDirichletContinuation_one
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ))
  (hρ : ρ ≠ 0) :
-- imply
  meromorphicOrderAt (linearAsymptoticDirichletContinuation a ρ) 1 =
    ((-1 : ℤ) : WithTop ℤ) := by
-- proof
  have hmero := meromorphicAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO
  have hval : linearAsymptoticNumerator a ρ 1 ≠ 0 := by
    rw [linearAsymptoticNumerator_one]; exact hρ
  exact ((meromorphicOrderAt_eq_int_iff (n := -1) hmero).2
    ⟨linearAsymptoticNumerator a ρ,
      analyticAt_linearAsymptoticNumerator a ρ hσ1 hO, hval,
      linearAsymptoticDirichletContinuation_eventuallyEq a ρ⟩)

/--
[tendsto_sub_one_mul_linearAsymptoticDirichletContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma tendsto_sub_one_mul_linearAsymptoticDirichletContinuation
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  Tendsto (fun s : ℂ =>
    (s - 1) * linearAsymptoticDirichletContinuation a ρ s)
    (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
-- proof
  have hnum : AnalyticAt ℂ (linearAsymptoticNumerator a ρ) 1 :=
    analyticAt_linearAsymptoticNumerator a ρ hσ1 hO
  have hlim : Tendsto (linearAsymptoticNumerator a ρ) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
    have h := hnum.continuousAt.tendsto
    rw [linearAsymptoticNumerator_one a ρ] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := by simpa using hs
    rw [linearAsymptoticDirichletContinuation_eq_inv_sub_mul a ρ hs1]
    unfold linearAsymptoticNumerator
    field_simp [sub_ne_zero.mpr hs1])

/--
[meromorphicOn_linearAsymptoticDirichletContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma meromorphicOn_linearAsymptoticDirichletContinuation
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  MeromorphicOn (linearAsymptoticDirichletContinuation a ρ)
    {s : ℂ | σ < s.re} := by
-- proof
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1
    exact meromorphicAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO
  · exact (analyticAt_linearAsymptoticDirichletContinuation_of_ne_one
    a ρ hO hs hs1).meromorphicAt

/--
[tendsto_linearAsymptoticDirichletContinuation_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
lemma tendsto_linearAsymptoticDirichletContinuation_Icc
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ))
  (hs : 1 < s.re) :
-- imply
  Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term a s n) atTop
    (𝓝 (linearAsymptoticDirichletContinuation a ρ s)) := by
-- proof
  have hrem := tendsto_abelContinuation_Icc (fun n => a n - ρ) (hσ1.trans hs)
    (isBigO_abelPartialSum_sub_const a ρ hO)
  have hrange := (tendsto_add_atTop_iff_nat 1).mpr (LSeriesHasSum_one hs).tendsto_sum_nat
  have hzeta : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
    LSeries.term (1 : ℕ → ℂ) s n) atTop (𝓝 (riemannZeta s)) := by
    have hconv : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1),
      LSeries.term (1 : ℕ → ℂ) s n) atTop (𝓝 (riemannZeta s)) := hrange
    have heq : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), LSeries.term (1 : ℕ → ℂ) s n =
      LSeries.term (1 : ℕ → ℂ) s 0 +
        ∑ n ∈ Finset.Icc 1 N, LSeries.term (1 : ℕ → ℂ) s n := by
      intro N
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_add_one_left_eq_Icc N.zero_le,
        Finset.sum_insert (by simp)]
      simp only [Nat.zero_add]
    simp only [LSeries.term_zero] at heq
    exact hconv.congr' (Filter.Eventually.of_forall fun N => (heq N).trans (zero_add _))
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, LSeries.term a s n =
    ρ * (∑ n ∈ Finset.Icc 1 N, LSeries.term (1 : ℕ → ℂ) s n) +
      ∑ n ∈ Finset.Icc 1 N, LSeries.term (fun n => a n - ρ) s n := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    simp only [LSeries.term_of_ne_zero hn0, Pi.one_apply, div_eq_mul_inv]
    ring
  have hlim := (hzeta.const_mul ρ).add hrem
  simpa only [linearAsymptoticDirichletContinuation] using
    hlim.congr' (Filter.Eventually.of_forall fun N => (hsplit N).symm)


-- created on 2026-10-20
-- updated on 2026-10-26
