/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle
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

/-- All semantic facts required of one actual directional merge record. -/
structure Valid (mode : Bool) (call : MergeMemoryCallEvent) : Prop where
  beforeActive : call.before.ActiveCore mode
  getmemActive : call.afterGetmem.ActiveCore mode
  afterMergeActive : call.afterMerge.ActiveCore mode
  requestWord : call.request = BitVec.ofNat 64 (min call.na call.nb)
  requestNonnegative : call.request.Nonnegative
  directionalRequest :
    (call.direction = .lo ∧ call.request.toNat = call.na ∧
      call.na ≤ call.nb) ∨
    (call.direction = .hi ∧ call.request.toNat = call.nb ∧
      call.nb < call.na)
  trimmingOnlyShrinks :
    call.na + call.nb ≤
      call.sourceLeftLength.toNat + call.sourceRightLength.toNat
  sourceRunsWithinList :
    call.sourceLeftLength.toNat + call.sourceRightLength.toNat ≤
      call.listlen.toNat
  smallerHalf :
    call.request.toNat ≤ (call.na + call.nb) / 2 ∧
      (call.na + call.nb) / 2 ≤ call.listlen.toNat / 2
  keyedLimit : call.before.hasValues = true →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2 ^ 59 - 1
  unkeyedLimit : call.before.hasValues = false →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2 ^ 60 - 1
  requestWithinLimit : call.request.toNat ≤ call.before.allocationLimit
  getmem : call.GetmemValid
  neverGuardRejected : call.outcome ≠ .guardRejected
  requestFits : call.request.toNat ≤ call.afterGetmem.alloced.toNat
  keySlots : ∀ i, i < call.request.toNat →
    i < call.afterGetmem.physicalSlots
  valueSlots : call.before.hasValues = true →
    ∀ i, i < call.request.toNat →
      call.afterGetmem.alloced.toNat + i <
        call.afterGetmem.physicalSlots
  mergeStorageFrame : call.MergeStorageFrame
  /-- Reuse preserves an already-established bound; growth establishes it
  from the exact allocation guard. -/
  physicalBoundPreserved : call.before.PhysicalBound →
    call.afterGetmem.PhysicalBound ∧ call.afterMerge.PhysicalBound

end MergeMemorySnapshot
end CPythonListsort
