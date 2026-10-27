import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.LargeSieveCorollary
open Finset Real LargeSieve


namespace LargeSieve

/--
[avgDeviationMod_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LargeSieveCorollary.lean)
-/
@[path]
lemma avgDeviationMod_nonneg
  {A : Finset ℕ}
  {p : ℕ} :
-- imply
  0 ≤ avgDeviationMod A p := by
-- proof
  unfold avgDeviationMod
  split_ifs with hp
  · linarith
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun a _ => abs_nonneg _)

end LargeSieve


-- created on 2026-10-23
