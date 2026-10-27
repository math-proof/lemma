import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalOSSS
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[decisionTree_atom_step_le_flip_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalOSSS.lean)
-/
@[path]
private lemma decisionTree_atom_step_le_flip_sum_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {base : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone T.evalR) :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) (∑ left, ∑ right, |T.evalR right - T.evalR left| * tripleJointProb mu ∅ base left right S) ≤ ∑ e, ((if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e left + T.evalR right * Lindeberg.coord e right) * tripleJointProb mu ∅ base left right S) - (if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e right + T.evalR right * Lindeberg.coord e left) * crossTripleJointProb mu ∅ base left right S)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_atom_step_le_flip_sum mu hpos hmono T t hf base

/--
[common_flip_moment_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalOSSS.lean)
-/
@[path]
private lemma common_flip_moment_extendDecisionTreeTriple_eq
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
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) (∑ base, (if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e left + T.evalR right * Lindeberg.coord e right) * tripleJointProb mu ∅ base left right S)) = 2 * Lindeberg.mean mu (fun ω => T.evalR ω * Lindeberg.coord e ω) * flipBaseProb mu ∅ seed e S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.common_flip_moment_extendDecisionTreeTriple mu hpos hmu T seed t e

/--
[causalTripleJump_le_of_cross_flip_moment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalOSSS.lean)
-/
@[path]
private lemma causalTripleJump_le_of_cross_flip_moment_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmu : ∑ ω, mu ω = 1)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone T.evalR)
  (hcross : ∀ e, let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) 2 * (Lindeberg.mean mu T.evalR * Lindeberg.mean mu (Lindeberg.coord e)) * flipBaseProb mu ∅ seed e S ≤ ∑ base, (if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e right + T.evalR right * Lindeberg.coord e left) * crossTripleJointProb mu ∅ base left right S)) :
-- imply
  causalTripleJump mu T t seed ≤ 2 * ∑ e, Lindeberg.cov mu T.evalR (Lindeberg.coord e) * Lindeberg.mean mu (fun base => sharedStepIndicator T base t e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalTripleJump_le_of_cross_flip_moment mu hpos hmu hmono T hf seed t hcross

/--
[causalTripleJump_le_cov_sharedStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalOSSS.lean)
-/
@[path]
private lemma causalTripleJump_le_cov_sharedStep_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmu : ∑ ω, mu ω = 1)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone T.evalR) :
-- imply
  causalTripleJump mu T t seed ≤ 2 * ∑ e, Lindeberg.cov mu T.evalR (Lindeberg.coord e) * Lindeberg.mean mu (fun base => sharedStepIndicator T base t e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalTripleJump_le_cov_sharedStep mu hpos hmu hmono T hf seed t

/--
[adaptive_tree_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalOSSS.lean)
-/
@[path]
private lemma adaptive_tree_osss_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmu : ∑ ω, mu ω = 1)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone T.evalR) :
-- imply
  Lindeberg.var mu T.evalR ≤ ∑ e, LindebergTree.revealmentMu mu T e * Lindeberg.cov mu T.evalR (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.adaptive_tree_osss mu hpos hmu hmono T hf


-- created on 2026-10-23
