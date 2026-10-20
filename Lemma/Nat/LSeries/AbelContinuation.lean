import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.AbelContinuation
open Filter Asymptotics MeasureTheory Topology Set Complex


/--
[abelSummatory_eq_zero_of_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma abelSummatory_eq_zero_of_lt_one_eq
  {f : ℕ → ℂ}
  {t : ℝ}
-- given
  (ht : t < 1) :
-- imply
  abelSummatory f t = 0 := by
-- proof
  apply abelSummatory_eq_zero_of_lt_one f ht

/--
[locallyIntegrableOn_abelSummatory](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma locallyIntegrableOn_abelSummatory_eq
  {f : ℕ → ℂ} :
-- imply
  LocallyIntegrableOn (abelSummatory f) (Set.Ioi (0 : ℝ)) := by
-- proof
  apply locallyIntegrableOn_abelSummatory f

/--
[isBigO_abelSummatory_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma isBigO_abelSummatory_atTop_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
-- given
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  (abelSummatory f) =O[atTop] fun t : ℝ => (t ^ σ : ℝ) := by
-- proof
  apply isBigO_abelSummatory_atTop f hO

/--
[isBigO_abelSummatory_nhdsGT_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma isBigO_abelSummatory_nhdsGT_zero_eq
  {f : ℕ → ℂ}
  {b : ℝ} :
-- imply
  (abelSummatory f) =O[𝓝[>] (0 : ℝ)] fun t : ℝ => (t ^ (-b) : ℝ) := by
-- proof
  apply isBigO_abelSummatory_nhdsGT_zero f b

/--
[abelContinuation_eq_mul_mellin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma abelContinuation_eq_mul_mellin_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hs : σ < s.re)
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  abelContinuation f s = s * mellin (abelSummatory f) (-s) := by
-- proof
  apply abelContinuation_eq_mul_mellin f hs hO

/--
[differentiableAt_abelContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma differentiableAt_abelContinuation_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hs : σ < s.re)
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  DifferentiableAt ℂ (abelContinuation f) s := by
-- proof
  apply differentiableAt_abelContinuation f hs hO

/--
[analyticOn_abelContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma analyticOn_abelContinuation_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
-- given
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  AnalyticOn ℂ (abelContinuation f) {s | σ < s.re} := by
-- proof
  apply analyticOn_abelContinuation f hO

/--
[abelContinuation_eq_LSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma abelContinuation_eq_LSeries_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hσ : 0 ≤ σ)
  (hs : σ < s.re)
  (hS : LSeriesSummable f s)
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  abelContinuation f s = LSeries f s := by
-- proof
  apply abelContinuation_eq_LSeries f hσ hs hS hO

/--
[tendsto_abelContinuation_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
private lemma tendsto_abelContinuation_Icc_eq
  {f : ℕ → ℂ}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hs : σ < s.re)
  (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
-- imply
  Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term f s n) atTop
    (𝓝 (abelContinuation f s)) := by
-- proof
  apply tendsto_abelContinuation_Icc f hs hO


-- created on 2026-10-20
