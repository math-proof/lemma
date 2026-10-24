import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
open StatMech StatMech.OSSS StatMech.OSSS.PredictableTreeQuery


/--
[pathPrefix_eq_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PredictableTreeQuery.lean)
-/
@[path]
private lemma pathPrefix_eq_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
  {t : ℕ}
-- given
  (hagree : ∀ e ∈ pathPrefix T ω t, ω' e = ω e) :
-- imply
  pathPrefix T ω' t = pathPrefix T ω t := by
-- proof
  apply StatMech.OSSS.PredictableTreeQuery.pathPrefix_eq_of_agree T ω ω' t hagree

/--
[pathQuery_eq_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PredictableTreeQuery.lean)
-/
@[path]
private lemma pathQuery_eq_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
  {t : ℕ}
-- given
  (hagree : ∀ e ∈ pathPrefix T ω t, ω' e = ω e) :
-- imply
  pathQuery T ω' t = pathQuery T ω t := by
-- proof
  apply StatMech.OSSS.PredictableTreeQuery.pathQuery_eq_of_agree T ω ω' t hagree

/--
[pathPrefix_succ_eq_insert_query](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PredictableTreeQuery.lean)
-/
@[path]
private lemma pathPrefix_succ_eq_insert_query_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ} :
-- imply
  pathPrefix T ω (t + 1) = match pathQuery T ω t with := by
-- proof
  apply StatMech.OSSS.PredictableTreeQuery.pathPrefix_succ_eq_insert_query T ω t

/--
[freshAt_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PredictableTreeQuery.lean)
-/
@[path]
private lemma freshAt_eq_one_iff_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ}
  {e : E} :
-- imply
  freshAt T ω t e = 1 ↔ pathQuery T ω t = some e ∧ e ∉ pathPrefix T ω t := by
-- proof
  apply StatMech.OSSS.PredictableTreeQuery.freshAt_eq_one_iff T ω t e


-- created on 2026-10-23
