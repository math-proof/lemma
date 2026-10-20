import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Statistics.GaussMarkov
open Matrix
open MathlibExt.Probability.Statistics.GaussMarkov


/--
[gaussMarkov_covariance_minimality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/GaussMarkov.lean)
-/
@[path]
private lemma gaussMarkov_covariance_minimality_eq
  {m n : ℕ}
  {X : Matrix (Fin m) (Fin n) ℝ}
-- given
  (hX : IsUnit (Xᵀ * X)) :
-- imply
  let B := by
-- proof
  apply MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality X hX


-- created on 2026-10-20
