import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
open StatMech StatMech.OSSS StatMech.OSSS.DecisionTree


/--
[eval_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean)
-/
@[path]
private lemma eval_reindex_eq
  {T : DecisionTree I}
  {omega : ConfigSpace E}
-- given
  (iota : I -> E) :
-- imply
  (T.reindex iota).eval omega = T.eval (restrictConfig iota omega) := by
-- proof
  apply StatMech.OSSS.DecisionTree.eval_reindex iota T omega

/--
[evalR_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean)
-/
@[path]
private lemma evalR_reindex_eq
  {T : DecisionTree I}
  {omega : ConfigSpace E}
-- given
  (iota : I -> E) :
-- imply
  (T.reindex iota).evalR omega = T.evalR (restrictConfig iota omega) := by
-- proof
  apply StatMech.OSSS.DecisionTree.evalR_reindex iota T omega

/--
[queried_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean)
-/
@[path]
private lemma queried_reindex_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : DecisionTree I}
  {omega : ConfigSpace E}
-- given
  (iota : I -> E) :
-- imply
  (T.reindex iota).queried omega = (T.queried (restrictConfig iota omega)).image iota := by
-- proof
  apply StatMech.OSSS.DecisionTree.queried_reindex iota T omega

/--
[mem_queried_reindex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean)
-/
@[path]
private lemma mem_queried_reindex_iff_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : DecisionTree I}
  {omega : ConfigSpace E}
  {i : I}
-- given
  (iota : I -> E)
  (hiota : Function.Injective iota) :
-- imply
  iota i ∈ (T.reindex iota).queried omega ↔ i ∈ T.queried (restrictConfig iota omega) := by
-- proof
  apply StatMech.OSSS.DecisionTree.mem_queried_reindex_iff iota hiota T omega i

/--
[not_mem_queried_reindex_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean)
-/
@[path]
private lemma not_mem_queried_reindex_of_not_range_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : DecisionTree I}
  {omega : ConfigSpace E}
  {e : E}
-- given
  (iota : I -> E)
  (he : e ∉ Set.range iota) :
-- imply
  e ∉ (T.reindex iota).queried omega := by
-- proof
  apply StatMech.OSSS.DecisionTree.not_mem_queried_reindex_of_not_range iota T omega e he


-- created on 2026-10-23
