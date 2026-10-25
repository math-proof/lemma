import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseEngineApply
open Finset Real Filter Topology StatMech StatMech.Probability


/--
[roe_card_filter_eq_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngineApply.lean)
-/
@[path]
private lemma roe_card_filter_eq_erase_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (univ.filter (fun S : Finset ι => S.card ≠ 0)) = univ.erase (∅ : Finset ι) := by
-- proof
  apply StatMech.Probability.roe_card_filter_eq_erase

/--
[roe_rhoOptimise_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngineApply.lean)
-/
@[path]
private lemma roe_rhoOptimise_apply_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bph_RhoOptimise 2 := by
-- proof
  apply StatMech.Probability.roe_rhoOptimise_apply


-- created on 2026-10-23
