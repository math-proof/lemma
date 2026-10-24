import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.AdaptiveCausalCrossMomentClose
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[cross_flip_moment_extendDecisionTreeTriple_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossMomentClose.lean)
-/
@[path]
private lemma cross_flip_moment_extendDecisionTreeTriple_eq_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
  {t : ℕ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmu : ∑ ω, mu ω = 1) :
-- imply
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) (∑ base, (if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e right + T.evalR right * Lindeberg.coord e left) * crossTripleJointProb mu ∅ base left right S)) = 2 * (Lindeberg.mean mu T.evalR * Lindeberg.mean mu (Lindeberg.coord e)) * flipBaseProb mu ∅ seed e S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.cross_flip_moment_extendDecisionTreeTriple_eq mu hpos hmu T seed t e


-- created on 2026-10-23
