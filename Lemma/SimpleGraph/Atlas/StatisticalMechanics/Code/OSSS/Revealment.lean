import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
open Finset StatMech StatMech.OSSS StatMech.OSSS.Revealment


/--
[revealment_eq_reveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_eq_reveal_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E} :
-- imply
  revealment ν T e = reveal ν T e := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_eq_reveal ν T e

/--
[revealment_eq_prob_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_eq_prob_queried_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E} :
-- imply
  revealment ν T e = expect ν (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_eq_prob_queried ν T e

/--
[revealment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ revealment ν T e := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_nonneg hν T e

/--
[revealment_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  revealment ν T e ≤ 1 := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_le_one hν T e

/--
[sum_revealment_eq_expect_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma sum_revealment_eq_expect_card_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E} :
-- imply
  ∑ e, revealment ν T e = expect ν (fun ω => ((T.queried ω).card : ℝ)) := by
-- proof
  apply StatMech.OSSS.Revealment.sum_revealment_eq_expect_card ν T

/--
[card_queried_le_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma card_queried_le_depth_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  (T.queried ω).card ≤ depth T := by
-- proof
  apply StatMech.OSSS.Revealment.card_queried_le_depth T ω

/--
[sum_revealment_le_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma sum_revealment_le_depth_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  ∑ e, revealment ν T e ≤ (depth T : ℝ) := by
-- proof
  apply StatMech.OSSS.Revealment.sum_revealment_le_depth hν T

/--
[revealment_le_of_queried_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_le_of_queried_imp_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
  [DecidablePred P]
-- given
  (hν : IsProbWeight ν)
  (P : ConfigSpace E → Prop)
  (h : ∀ ω, e ∈ T.queried ω → P ω) :
-- imply
  revealment ν T e ≤ expect ν (fun ω => if P ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_le_of_queried_imp hν T e P h

/--
[revealment_le_of_queried_imp_or](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean)
-/
@[path]
private lemma revealment_le_of_queried_imp_or_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hν : IsProbWeight ν)
  (P Q : ConfigSpace E → Prop)
  (h : ∀ ω, e ∈ T.queried ω → P ω ∨ Q ω) :
-- imply
  revealment ν T e ≤ expect ν (fun ω => if P ω then (1 : ℝ) else 0) + expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.Revealment.revealment_le_of_queried_imp_or hν T e P Q h


-- created on 2026-10-23
