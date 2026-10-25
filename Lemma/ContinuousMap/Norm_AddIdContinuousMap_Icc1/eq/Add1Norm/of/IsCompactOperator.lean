import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.Daugavet

/--
[Daugavet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/Daugavet.lean)
-/
@[path]
private lemma daugavet_eq
-- given
  (T : ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ →L[ℝ] ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ)
  (hT : IsCompactOperator T) :
-- imply
  ‖ContinuousLinearMap.id ℝ (ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ) + T‖ = 1 + ‖T‖ := by
-- proof
  apply FunctionalAnalysis.DaugavetWanted.daugavet T hT

-- created on 2026-10-10
