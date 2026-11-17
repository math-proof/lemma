import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.MergeForceCollapseSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.TopLevelErasure
open CPythonListsort


namespace CPythonListsort

/--
[erase_mergeForceCollapseLoopTraced_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureForceCollapse.lean)
-/
@[path]
lemma erase_mergeForceCollapseLoopTraced_of_mergeAt
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
-- given
  (hMergeAt : ∀ (state : MergeState κ ν) (i : Nat), (mergeAtTraced? state i).erase = mergeAt? state i) :
-- imply
  (mergeForceCollapseLoopTraced? fuel state).erase = mergeForceCollapseLoop? fuel state := by
-- proof
  induction fuel generalizing state with
  | zero =>
    simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
    by_cases hdone : state.pending.size ≤ 1
    · rw [ite_eq_left hdone, ite_eq_left hdone]
      rfl
    · rw [ite_eq_right hdone, ite_eq_right hdone]
      simp [TraceResult.erase_markFuelExhausted]
      rfl
  | succ fuel ih =>
    simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
    by_cases hmany : 1 < state.pending.size
    · rw [ite_eq_left hmany, ite_eq_left hmany, TraceResult.erase_bind,
      erase_forceCollapseIndexTraced]
      cases hindex : forceCollapseIndex? state with
      | none => simp
      | some i =>
        simp only [Option.bind_some, TraceResult.erase_bind,
          hMergeAt]
        cases hmerged : mergeAt? state i with
        | none => simp
        | some merged =>
          simp only [Option.bind_some]
          by_cases hContinue :
            merged.returnCode = 0 ∧ !merged.fuelExhausted
          · rw [ite_eq_left hContinue, ite_eq_left hContinue]
            exact ih merged.state
          · rw [ite_eq_right hContinue, ite_eq_right hContinue]
            rfl
    · rw [ite_eq_right hmany, ite_eq_right hmany]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeForceCollapseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureForceCollapse.lean)
-/
@[path]
lemma erase_mergeForceCollapseTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state := by
-- proof
  exact erase_mergeForceCollapseLoopTraced_of_mergeAt erase_mergeAtTraced
    state.pending.size state

end CPythonListsort


-- created on 2026-10-23
