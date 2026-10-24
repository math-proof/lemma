/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/PushRunPreservation.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.AccessTrace
import Lemma.List.Atlas.CPythonListsort.Code.Policy.StackDepth

/-!
# Policy preservation across the pending-run push

The caller of `found_new_run` performs an unconditional `Array.push`.  Given
the policy facts established just before that call site, this file proves that
the enlarged stack tiles the enlarged scanned prefix and again has a
`PoweredPrefix`: all old entries form the initialized prefix and the new top's
stored power remains deliberately unconstrained.

The operation itself is total on every modeled state.  `ReadyToPush` appears
only on the preservation and capacity theorem; it is not consulted by either
the ordinary or traced implementation.
-/

namespace CPythonListsort

universe u v

/-- The unconditional source push extends the valid pending tiling by exactly
the newly discovered adjacent run. -/
theorem pushPendingRun_preserves_pendingLayout
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    PendingLayout (pushPendingRun state newRun)
      (scanned + newRun.len.toNat) := by
  rcases hready.layout with
    ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩
  rcases hready.new_run_nonempty with ⟨hnewNonnegative, hnewPositive⟩
  have hcover' := hcover.appendSingleton hready.new_run_adjacent
    hnewNonnegative hnewPositive
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [pushPendingRun] using hlistNonnegative
  · simpa [pushPendingRun] using hdataBound
  · simpa [pushPendingRun] using hready.new_run_within_input
  · simpa [pushPendingRun, Nat.add_assoc] using hcover'
