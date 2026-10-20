import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.GreatPicard
open Set Filter Topology Metric
open MathlibExt.Analysis.Complex.GreatPicardWanted


/--
[greatPicard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/GreatPicard.lean)
-/
@[path]
private lemma greatPicard_eq
  {f : ℂ → ℂ}
  {c : ℂ}
-- given
  (hf : IsEssentialIsolatedSingularityAt f c) :
-- imply
  Set.Subsingleton
    {w : ℂ | ∃ r : ℝ, 0 < r ∧ Set.Finite {z ∈ Metric.ball c r \ {c} | f z = w}} := by
-- proof
  apply MathlibExt.Analysis.Complex.GreatPicardWanted.greatPicard hf


-- created on 2026-10-20
