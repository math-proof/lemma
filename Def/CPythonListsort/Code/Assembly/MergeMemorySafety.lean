/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Structure.CPythonListsort.Code.Assembly.MergeMemorySafety
/-!
# Aggregate temporary merge-memory safety

This module is the public projection of the literal merge-memory history
carried by `listSortImplTraced?`.  It does not define another evaluator or a
separately supplied history: every lifecycle field below refers directly to
the `memoryEvents` stored in the actual top-level execution trace.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Concrete total Boolean comparator used only by the executable witnesses. -/
def natLt (left right : Nat) : Bool := decide (left < right)

/-- Empty ordinary-array input with a fixed payload universe. -/
def emptyUnkeyed : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs #[]

/-- Empty keyed input; its mode bit remains observable even though the
entrywise values-mode invariant is vacuous. -/
def emptyKeyed : ListSortInput Nat Nat :=
  ListSortInput.keyed #[]

/-- Two increasing natural runs whose boundary descends, so the top-level
scan discovers two distinct runs before final collapse. -/
def twoRunKeys (leftLength rightLength : Nat) : Array Nat :=
  (Array.range leftLength |>.map fun key => 1000 + key) ++
    Array.range rightLength

/-- Equal 33-element runs force the left-to-right merge direction. -/
def loInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 33)

/-- A 33-element left run and 32-element right run force the right-to-left
merge direction. -/
def hiInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 32)

/-- Observable directional-call projection of the literal top-level trace. -/
def directions {payload : Type} (input : ListSortInput Nat payload) :
    List MergeMemoryDirection :=
  (listSortTraced? natLt false input).trace.memoryEvents.filterMap fun
    | .mergeCall call => some call.direction
    | _ => none

/-- One increasing keyed run used by the repeated-growth fixture. -/
def keyedRun (base length : Nat) : Array (Nat × Nat) :=
  (Array.range length).map fun offset =>
    let key := base + offset
    (key, key)

/-- Four descending-by-block 129-element keyed runs.  The first pair grows
past keyed inline capacity 128; the final 258/258 merge then frees that heap
buffer and grows again. -/
def releasedGrowthInput : ListSortInput Nat Nat :=
  ListSortInput.keyed
    (keyedRun 3000 129 ++ keyedRun 2000 129 ++
      keyedRun 1000 129 ++ keyedRun 0 129)

/-- For every actual directional call, retain the optional freed backing,
the post-`merge_getmem` backing, and its logical cell count. -/
def growthSummaries :
    List (Option TempBacking × TempBacking × Nat) :=
  (listSortTraced? natLt false releasedGrowthInput).trace.memoryEvents.filterMap
    fun
      | .mergeCall call =>
          some (call.intermediateFree.map (·.backing),
            call.afterGetmem.backing, call.afterGetmem.cellsSize)
      | _ => none

end CPythonListsort
