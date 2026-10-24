import Mathlib
import sympy.Basic


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
    · rw [if_pos hdone, if_pos hdone]
      rfl
    · rw [if_neg hdone, if_neg hdone]
      simp [TraceResult.erase_markFuelExhausted]
      rfl
  | succ fuel ih =>
    simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
    by_cases hmany : 1 < state.pending.size
    · rw [if_pos hmany, if_pos hmany, TraceResult.erase_bind,
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
          · rw [if_pos hContinue, if_pos hContinue]
            exact ih merged.state
          · rw [if_neg hContinue, if_neg hContinue]
            rfl
    · rw [if_neg hmany, if_neg hmany]
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
