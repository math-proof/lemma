import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.KreinRutman

open scoped ENNReal

/--
[KreinRutman](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/KreinRutman.lean)
-/
@[path]
private lemma krein_rutman_eq
-- given
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (T : ContinuousLinearMap (RingHom.id ℝ) (ContinuousMap K ℝ) (ContinuousMap K ℝ))
  (hT_compact : IsCompactOperator T)
  (hT_pos : ∀ f : ContinuousMap K ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (T f) x)
  (hr : (0 : ℝ≥0∞) < spectralRadius ℝ T) :
-- imply
  ∃ f : ContinuousMap K ℝ, f ≠ 0 ∧ (∀ x, 0 ≤ f x) ∧ T f = (spectralRadius ℝ T).toReal • f := by
-- proof
  apply FunctionalAnalysis.KreinRutmanWanted.krein_rutman T hT_compact hT_pos hr

-- created on 2026-10-10
