import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.AsymptoticContinuation
open Filter Asymptotics Topology


/--
[abelPartialSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma abelPartialSum_sub_const_eq
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {n : ℕ} :
-- imply
  abelPartialSum (fun k => a k - ρ) n = abelPartialSum a n - n • ρ := by
-- proof
  apply abelPartialSum_sub_const a ρ n

/--
[isBigO_abelPartialSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma isBigO_abelPartialSum_sub_const_eq
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  (fun n => abelPartialSum (fun k => a k - ρ) n) =O[atTop]
    fun n => ((n : ℝ) ^ σ : ℝ) := by
-- proof
  apply isBigO_abelPartialSum_sub_const a ρ hO

/--
[analyticAt_linearAsymptoticDirichletContinuation_of_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma analyticAt_linearAsymptoticDirichletContinuation_of_ne_one_eq
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
  apply analyticAt_linearAsymptoticDirichletContinuation_of_ne_one a ρ hO hs hs1

/--
[linearAsymptoticDirichletContinuation_eq_inv_sub_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma linearAsymptoticDirichletContinuation_eq_inv_sub_mul_eq
  {a : ℕ → ℂ}
  {ρ s : ℂ}
-- given
  (hs : s ≠ 1) :
-- imply
  linearAsymptoticDirichletContinuation a ρ s =
    (s - 1)⁻¹ *
    (ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s) := by
-- proof
  apply linearAsymptoticDirichletContinuation_eq_inv_sub_mul a ρ hs

/--
[meromorphicAt_linearAsymptoticDirichletContinuation_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma meromorphicAt_linearAsymptoticDirichletContinuation_one_eq
  {a : ℕ → ℂ}
  {ρ : ℂ}
  {σ : ℝ}
-- given
  (hσ1 : σ < 1)
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  MeromorphicAt (linearAsymptoticDirichletContinuation a ρ) 1 := by
-- proof
  apply meromorphicAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO

/--
[meromorphicOrderAt_linearAsymptoticDirichletContinuation_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma meromorphicOrderAt_linearAsymptoticDirichletContinuation_one_eq
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
  apply meromorphicOrderAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO hρ

/--
[tendsto_sub_one_mul_linearAsymptoticDirichletContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma tendsto_sub_one_mul_linearAsymptoticDirichletContinuation_eq
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
  apply tendsto_sub_one_mul_linearAsymptoticDirichletContinuation a ρ hσ1 hO

/--
[meromorphicOn_linearAsymptoticDirichletContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma meromorphicOn_linearAsymptoticDirichletContinuation_eq
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
  apply meromorphicOn_linearAsymptoticDirichletContinuation a ρ hσ1 hO

/--
[tendsto_linearAsymptoticDirichletContinuation_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
private lemma tendsto_linearAsymptoticDirichletContinuation_Icc_eq
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
  apply tendsto_linearAsymptoticDirichletContinuation_Icc a ρ hσ1 hO hs


-- created on 2026-10-20
