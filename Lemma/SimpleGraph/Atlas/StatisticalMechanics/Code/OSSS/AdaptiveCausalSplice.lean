import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalSplice
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[mem_take_realizedEquiv_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalSplice.lean)
-/
@[path]
private lemma mem_take_realizedEquiv_iff_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {i : Fin (Fintype.card E)}
  {t : ℕ} :
-- imply
  realizedEquiv S base i ∈ (realizedList S base).take t ↔ (i : ℕ) < t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.mem_take_realizedEquiv_iff S base i t

/--
[causalMixLabels_extendDecisionTreeAt_eq_adaptWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalSplice.lean)
-/
@[path]
private lemma causalMixLabels_extendDecisionTreeAt_eq_adaptWt_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ} :
-- imply
  causalMixLabels (extendDecisionTreeAt t T base (Finset.univ : Finset E)) base U V = AdaptMConditional.adaptWt U V (T.queried base).card t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_extendDecisionTreeAt_eq_adaptWt t T base U V

/--
[causalMixLabels_extendDecisionTreeTriple_left_eq_adaptWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalSplice.lean)
-/
@[path]
private lemma causalMixLabels_extendDecisionTreeTriple_left_eq_adaptWt_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ} :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) causalMixLabels S.leftOrder base U V = AdaptMConditional.adaptWt U V (T.queried base).card t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_extendDecisionTreeTriple_left_eq_adaptWt t T base U V

/--
[causalMixLabels_extendDecisionTreeTriple_right_eq_adaptWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalSplice.lean)
-/
@[path]
private lemma causalMixLabels_extendDecisionTreeTriple_right_eq_adaptWt_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ} :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) causalMixLabels S.rightOrder base U V = AdaptMConditional.adaptWt U V (T.queried base).card (t + 1) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_extendDecisionTreeTriple_right_eq_adaptWt t T base U V


-- created on 2026-10-23
