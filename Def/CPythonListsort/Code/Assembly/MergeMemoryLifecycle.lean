/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
/-!
# Semantic validation for the real merge-memory trace

`AccessTrace` deliberately stores raw, type-erased observations.  This module
states the propositions those observations must satisfy.  None of the
predicates below changes the evaluator or manufactures a reachability
relation: later assembly theorems apply them to the literal `memoryEvents`
field returned by `listSortImplTraced?`.
-/


namespace CPythonListsort

universe u v

namespace MergeMemorySnapshot

/-- The one-or-two-pointer multiplier represented by a raw snapshot. -/
def multiplier (snapshot : MergeMemorySnapshot) : Nat :=
  if snapshot.hasValues then 2 else 1

/-- Snapshot form of the signed-allocation guard limit. -/
def allocationLimit (snapshot : MergeMemorySnapshot) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / snapshot.multiplier

/-- Literal snapshot form of `TempStorageInv`.  The released case
deliberately leaves `alloced` and `hasValues` stale. -/
def StorageInv (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots = snapshot.multiplier * snapshot.cellsSize ∧
    match snapshot.backing with
    | .inline =>
        snapshot.cellsSize = snapshot.alloced.toNat ∧
          snapshot.multiplier * snapshot.alloced.toNat ≤
            MERGESTATE_TEMP_SIZE
    | .heap => snapshot.cellsSize = snapshot.alloced.toNat
    | .released => snapshot.cellsSize = 0

/-- Snapshot backing is available for payload access. -/
def Live (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.backing ≠ .released

/-- Every main-array entry agrees with the retained values-pointer mode.
The separate Boolean equation is intentional: on an empty main array the
entrywise clause alone cannot determine the mode. -/
def ValuesMode (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.hasValues = mode ∧
    ∀ (i : Nat) (hi : i < snapshot.mainValuePresent.length),
      snapshot.mainValuePresent[i] = mode

/-- The active representation facts, excluding the selected-platform heap
upper bound.  That bound is a reachability fact threaded separately from the
inline initializer through each real allocation transition. -/
def ActiveCore (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.StorageInv ∧ snapshot.Live ∧
    snapshot.cellsSize = snapshot.alloced.toNat ∧
    snapshot.ValuesMode mode

/-- The selected-platform physical allocation ceiling. -/
def PhysicalBound (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

/-- The intermediate released snapshot which the C control flow exposes when
`merge_getmem` leaves the signed-capacity reuse branch.  This is a raw
observation constructor: the semantic lemmas below prove that its `some`
case is exactly the state immediately after `mergeFreemem`. -/
def mergeMemoryIntermediateFree (state : MergeState κ ν) (need : PySSize) :
    Option MergeMemorySnapshot :=
  if need.sle state.alloced then none
  else some (MergeMemorySnapshot.ofState (mergeFreemem state))

/-- Raw lifecycle observation for one completed `merge_lo` call. -/
def mergeLoMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeLoResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.na
  let allocated := mergeLoAllocated call
  { direction := .lo
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Raw lifecycle observation for one completed `merge_hi` call. -/
def mergeHiMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeHiResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.nb
  let allocated := mergeHiAllocated call
  { direction := .hi
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Snapshot-level record of the exact `merge_freemem` transition which
precedes a growing (or guard-rejected) allocation attempt. -/
def IsFreedFrom (before freed : MergeMemorySnapshot) : Prop :=
  freed.hasValues = before.hasValues ∧
    freed.alloced = before.alloced ∧
    freed.mainValuePresent = before.mainValuePresent ∧
    if before.backing = .inline then
      freed = before
    else
      freed.backing = .released ∧ freed.cellsSize = 0 ∧
        freed.physicalSlots = 0

/-- Exact successful `merge_getmem` behavior visible in a call record.
The rejected branch is deliberately absent; later proofs must derive one of
these two arms from the pending-layout request bound. -/
def GetmemValid (call : MergeMemoryCallEvent) : Prop :=
  (call.outcome = .reused ∧
      call.request.sle call.before.alloced = true ∧
      call.intermediateFree = none ∧
      call.afterGetmem = call.before) ∨
    (call.outcome = .grown ∧
      call.request.sle call.before.alloced = false ∧
      ∃ freed,
        call.intermediateFree = some freed ∧
        IsFreedFrom call.before freed ∧
        call.request.toNat ≤ call.before.allocationLimit ∧
        call.afterGetmem.backing = .heap ∧
        call.afterGetmem.hasValues = call.before.hasValues ∧
        call.afterGetmem.alloced = call.request ∧
        call.afterGetmem.cellsSize = call.request.toNat ∧
        call.afterGetmem.physicalSlots =
          call.before.multiplier * call.request.toNat ∧
        call.afterGetmem.mainValuePresent =
          call.before.mainValuePresent)

/-- The merge proper can change main-data order and temporary contents, but
not the allocation metadata installed by `merge_getmem`. -/
def MergeStorageFrame (call : MergeMemoryCallEvent) : Prop :=
  call.afterMerge.backing = call.afterGetmem.backing ∧
    call.afterMerge.hasValues = call.afterGetmem.hasValues ∧
    call.afterMerge.cellsSize = call.afterGetmem.cellsSize ∧
    call.afterMerge.alloced = call.afterGetmem.alloced ∧
    call.afterMerge.physicalSlots = call.afterGetmem.physicalSlots ∧
    call.afterMerge.mainValuePresent.length =
      call.afterGetmem.mainValuePresent.length

end MergeMemorySnapshot
end CPythonListsort
