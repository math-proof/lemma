/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PendingLayout.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
/-!
# Pending-run layout

The invariant deliberately mentions only run positions and lengths. Powers,
comparators, sorting properties, and the eventual stack-capacity theorem are
kept in their own policy and correctness nodes.
-/


namespace CPythonListsort

universe u

/-- The first index after a pending run. -/
def PendingRun.endIndex (run : PendingRun) : Nat :=
  run.base + run.len.toNat

/-- A run list covers `[cursor, limit)` without gaps or empty runs. -/
def PendingRunsCover : Nat → Nat → List PendingRun → Prop
  | cursor, limit, [] => cursor = limit
  | cursor, limit, run :: rest =>
      run.base = cursor ∧
        run.len.Nonnegative ∧
        0 < run.len.toNat ∧
        run.endIndex ≤ limit ∧
        PendingRunsCover run.endIndex limit rest

/-- Pending runs are nonempty, in the input region, consecutive, and cover
exactly the already-scanned prefix beginning at `basekeys`. -/
def PendingLayout (state : MergeState κ ν) (scanned : Nat) : Prop :=
  state.listlen.Nonnegative ∧
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size ∧
    scanned ≤ state.listlen.toNat ∧
    PendingRunsCover state.basekeys (state.basekeys + scanned)
      state.pending.toList

end CPythonListsort
