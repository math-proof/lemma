/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeTracePrimitives
import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemStorageValid
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety

/-!
# `merge_lo` lockstep safety

This module instruments the reviewed `merge_lo` transcription with the typed
main-data and temporary-storage primitives from `MergeTracePrimitives`.
Temporary gallops read their actual temporary backing directly; the
materialized `SortSlice` is used only as an untraced semantic bridge to the
reviewed evaluator.
-/

namespace CPythonListsort

universe u v w

variable {κ : Type u} {ν : Type v}

/-! ## Classified bulk-copy permits -/

/-- Provenance permit consumed by the initial main-to-temporary copy. -/
theorem mergeLoInitialDataToTempPermit :
    (MergeMemcpySite.lo .initialDataToTemp).MainToTempPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by an A-side gallop block copy. -/
theorem mergeLoGallopTempToDataPermit :
    (MergeMemcpySite.lo .gallopTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by the final A-side remainder copy. -/
theorem mergeLoFinalTempToDataPermit :
    (MergeMemcpySite.lo .finalTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-! ## Trace-preserving control helpers -/

/-- Lift an already-reviewed partial, non-accessing computation into the trace
monad. -/
def mergeLoTraceOption : Option α → TraceResult α
  | none => TraceResult.failure
  | some value => TraceResult.pure value

/-- Record that the outer merge driver, or a nested gallop, exhausted fuel. -/
def mergeLoFuelFailureTraced (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  (TraceResult.pure (mergeLoOutOfFuel machine.state)).markFuelExhausted

/-! ## One-step movement -/

/-- Copy one left-run entry from temporary storage and advance forward. -/
def mergeLoCopyAIncrTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoMachine κ ν) :=
  (tempToMainCellTraced? machine.state machine.dest (Int.ofNat machine.aPos)).map
    fun state =>
      { machine with
        state := state
        dest := machine.dest + 1
        aPos := machine.aPos + 1
        na := machine.na - 1 }

/-- Copy one right-run entry within main data and advance forward. -/
def mergeLoCopyBIncrTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoMachine κ ν) :=
  (mainDataMemmoveTraced? machine.state machine.dest machine.bPos 1).map
    fun state =>
    { machine with
      state := state
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }

/-- The successful tail copies the unconsumed temporary remainder. -/
def mergeLoSucceedTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  (tempToMainMemcpyTraced? (.lo .finalTempToData)
      mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
      (Int.ofNat machine.aPos)).map mergeLoSuccess

/-- The `CopyB` label shifts the right remainder and installs the unique
remaining left entry. -/
def mergeLoCopyBTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  if machine.na = 1 ∧ 0 < machine.nb then
    (mainDataMemmoveTraced? machine.state machine.dest machine.bPos
        machine.nb).bind fun state =>
      (tempToMainCellTraced? state
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).map mergeLoSuccess
  else
    TraceResult.failure

/-! ## Galloping and outer driver -/

/-- One traced galloping iteration.  The A-side search uses the physical
temporary source.  `activeA` is materialized without trace solely to relate the
direct-source gallop to the reviewed `gallopRight?` call during erasure. -/
def mergeLoGallopRoundTraced?
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat →
      TraceResult (MergeLoResult κ ν)) :
    TraceResult (MergeLoResult κ ν) :=
  if machine.na ≤ 1 ∨ machine.nb = 0 then
    TraceResult.failure
  else
    let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else
        machine.minGallop
    let state := { machine.state with min_gallop := minGallop }
    let machine := { machine with state := state, minGallop := minGallop }
    (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
      fun firstB =>
        (mergeLoTraceOption
          (mergeLoTempRun? machine.state.a machine.aPos machine.na)).bind
          fun _activeA =>
            (gallopRightTraced? machine.state
              (.temporary machine.state.a (Int.ofNat machine.aPos))
              firstB.key machine.na 0).bind fun gallopA =>
              if gallopA.fuelExhausted then
                mergeLoFuelFailureTraced machine
              else
                let aCount := gallopA.index
                if aCount > machine.na then
                  TraceResult.failure
                else
                  (tempToMainMemcpyTraced? (.lo .gallopTempToData)
                    mergeLoGallopTempToDataPermit aCount machine.state
                    machine.dest (Int.ofNat machine.aPos)).bind fun state =>
                    let machine : MergeLoMachine κ ν :=
                      { machine with
                        state := state
                        dest := machine.dest + Int.ofNat aCount
                        aPos := machine.aPos + aCount
                        na := machine.na - aCount }
                    if machine.na = 0 then
                      mergeLoSucceedTraced? machine
                    else if machine.na = 1 then
                      mergeLoCopyBTraced? machine
                    else
                      (mergeLoCopyBIncrTraced? machine).bind fun machine =>
                        if machine.nb = 0 then
                          mergeLoSucceedTraced? machine
                        else
                          (TraceResult.tempPayloadRead? machine.state.a
                            (Int.ofNat machine.aPos)).bind fun firstA =>
                            (gallopLeftTraced? machine.state
                              (.main machine.state.data machine.bPos)
                              firstA.key machine.nb 0).bind fun gallopB =>
                              if gallopB.fuelExhausted then
                                mergeLoFuelFailureTraced machine
                              else
                                let bCount := gallopB.index
                                if bCount > machine.nb then
                                  TraceResult.failure
                                else
                                  (mainDataMemmoveTraced? machine.state
                                    machine.dest machine.bPos bCount).bind
                                    fun state =>
                                      let machine : MergeLoMachine κ ν :=
                                        { machine with
                                          state := state
                                          dest := machine.dest + Int.ofNat bCount
                                          bPos := machine.bPos + Int.ofNat bCount
                                          nb := machine.nb - bCount }
                                      if machine.nb = 0 then
                                        mergeLoSucceedTraced? machine
                                      else
                                        (mergeLoCopyAIncrTraced? machine).bind
                                          fun machine =>
                                            if machine.na = 1 then
                                              mergeLoCopyBTraced? machine
                                            else
                                              next machine aCount bCount

/-- Fuel-bounded traced phase driver. -/
def mergeLoLoopTraced? :
    Nat → MergeLoMachine κ ν → MergeLoPhase →
      TraceResult (MergeLoResult κ ν)
  | 0, machine, _ => mergeLoFuelFailureTraced machine
  | fuel + 1, machine, .ordinary aCount bCount =>
      if machine.na ≤ 1 ∨ machine.nb = 0 then
        TraceResult.failure
      else
        (TraceResult.tempPayloadRead? machine.state.a
          (Int.ofNat machine.aPos)).bind fun firstA =>
          (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
            fun firstB =>
              if iflt machine.state.key_compare firstB.key firstA.key then
                (mergeLoCopyBIncrTraced? machine).bind fun machine =>
                  let bCount := bCount + 1
                  if machine.nb = 0 then
                    mergeLoSucceedTraced? machine
                  else if mergeLoCountAtLeastWord bCount machine.minGallop then
                    mergeLoLoopTraced? fuel
                      { machine with minGallop := machine.minGallop + 1 }
                      .galloping
                  else
                    mergeLoLoopTraced? fuel machine (.ordinary 0 bCount)
              else
                (mergeLoCopyAIncrTraced? machine).bind fun machine =>
                  let aCount := aCount + 1
                  if machine.na = 1 then
                    mergeLoCopyBTraced? machine
                  else if mergeLoCountAtLeastWord aCount machine.minGallop then
                    mergeLoLoopTraced? fuel
                      { machine with minGallop := machine.minGallop + 1 }
                      .galloping
                  else
                    mergeLoLoopTraced? fuel machine (.ordinary aCount 0)
  | fuel + 1, machine, .galloping =>
      mergeLoGallopRoundTraced? machine fun machine aCount bCount =>
        if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
          mergeLoLoopTraced? fuel machine .galloping
        else
          let minGallop := machine.minGallop + 1
          let state := { machine.state with min_gallop := minGallop }
          mergeLoLoopTraced? fuel
            { machine with state := state, minGallop := minGallop }
            (.ordinary 0 0)

/-! ## Public traced evaluator -/

/-- A genuine instrumented execution of `merge_lo`.  Allocation itself has no
array access event; every subsequent movement and comparison access is routed
through a typed primitive. -/
def mergeLoTraced? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    TraceResult (MergeLoResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 na)
    if allocated.outcome = .guardRejected then
      TraceResult.pure (mergeLoFailure allocated.state)
    else
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit na allocated.state 0 ssa).bind fun state =>
        let machine : MergeLoMachine κ ν :=
          { state := state
            dest := ssa
            aPos := 0
            bPos := ssb
            na := na
            nb := nb
            minGallop := state.min_gallop }
        (mergeLoCopyBIncrTraced? machine).bind fun machine =>
          if machine.nb = 0 then
            mergeLoSucceedTraced? machine
          else if machine.na = 1 then
            mergeLoCopyBTraced? machine
          else
            mergeLoLoopTraced? (na + nb + 1) machine (.ordinary 0 0)
  else
    TraceResult.failure

/-! ## Absence of nested merge-memory and policy events -/

/-- A local trace fragment contains neither a top-level merge-memory boundary
nor a merge-policy event.  Keeping the two channels together makes the
structural induction below the single source of truth for both absence
claims. -/
private def MergeLoMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

/-! ## Public safety vocabulary -/

/-- State fields that `merge_lo` is not allowed to mutate.  `min_gallop` is
intentionally absent; it is the merge's adaptive output. -/
structure MergeLoStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeLoStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_lo`.  Payload cells may change during the
initial main-to-temporary copy, so this frame deliberately records their
extent rather than their contents. -/
structure MergeLoStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeLoStorageFrame

/-- Inductive invariant for every live left-to-right merge machine.  The three
cursor equalities are the exact arithmetic preserved by cell and block moves. -/
structure MergeLoMachineInvariant (origin : MergeState κ ν)
    (tempTotal : Nat) (endIndex : Int) (machine : MergeLoMachine κ ν) : Prop where
  destNonnegative : 0 ≤ machine.dest
  tempAccounting : machine.aPos + machine.na = tempTotal
  adjacency : machine.dest + Int.ofNat machine.na = machine.bPos
  rightAccounting : machine.bPos + Int.ofNat machine.nb = endIndex
  mainEnd : endIndex ≤ Int.ofNat machine.state.data.entries.size
  leftWordBound : machine.na ≤ PY_LIST_MAX
  rightWordBound : machine.nb ≤ PY_LIST_MAX
  tempCapacity : tempTotal ≤ machine.state.a.cells.size
  tempValuesMode : TempRangeValuesMode machine.state.a 0 tempTotal
  tempInvariant : TempStorageInv machine.state.a machine.state.alloced
  tempLive : machine.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant machine.state.a.hasValues machine.state.data
  stableFrame : MergeLoStableFrame origin machine.state
  storageFrame : MergeLoStorageFrame origin machine.state

/-- The loop fuel stays strictly ahead of the number of unmerged cells. -/
def MergeLoFuelInvariant (fuel : Nat) (machine : MergeLoMachine κ ν) : Prop :=
  machine.na + machine.nb < fuel

namespace MergeLoMachineInvariant

/-! ## Internal lockstep postconditions -/

/-- Postcondition threaded through the terminal helpers and the recursive
driver.  Its reference argument is the exact reviewed fragment represented by
the traced execution. -/
structure MergeLoCorePost
    (origin : MergeState κ ν) (tempTotal : Nat)
    (execution : TraceResult (MergeLoResult κ ν))
    (reference : Option (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempCapacity : tempTotal ≤ result.state.a.cells.size
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeLoStableFrame origin result.state
  storageFrame : MergeLoStorageFrame origin result.state

/-- The allocation selected by the concrete `merge_lo` call site.  Naming it
once keeps the preparation, core-execution, and final trace-witness stages in
lockstep without repeating the `merge_getmem` expression. -/
def mergeLoAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.na)

/-- Full externally consumable postcondition for one actual `merge_at`
`merge_lo` continuation. -/
structure MergeLoSafetyPost
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  noMemoryEvents : execution.trace.memoryEvents = []
  exactErasure : execution.erase =
    mergeLo? call.state call.ssa call.ssb call.na call.nb
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : call.na ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeLoStableFrame call.state result.state
  geometry : MergeAtSafetyGeometry pre scanned i call
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.na call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  /-- The exact `merge_getmem` certificate for the allocation consumed by
  this merge, including reuse/growth accounting and the intermediate free on
  growth. -/
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
  /-- Every item of temporary-storage metadata is unchanged from the
  successful allocation through the final merge state. -/
  postGetmemStorageFrame :
    MergeLoStorageFrame (mergeLoAllocated call).state result.state
  /-- Reuse preserves the incoming physical bound exactly; growth establishes
  it from the allocation guard.  The top-level lifecycle induction supplies
  the bound on the reuse input. -/
  physicalSlotsBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  /-- Full provenance obligation inherited from the classified initial copy.
  Besides distinct backing at every merge call site, this exports the generic
  SortSlice admissibility theorem and the same-backing-overlap rejection
  regression consumed by downstream merge-memory safety. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent : execution.trace.HasAccess .read .inputKeys
  tempWriteEvent : execution.trace.HasTempAccess .write
  tempReadEvent : execution.trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    execution.trace.HasAccess .read .synchronizedValues

/-! ## Staged public-proof assembly -/

/-- Initial machine installed after the left run has been copied to temporary
storage. -/
def mergeLoInitialMachine (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : MergeLoMachine κ ν :=
  { state := state
    dest := call.ssa
    aPos := 0
    bPos := call.ssb
    na := call.na
    nb := call.nb
    minGallop := state.min_gallop }

/-- Exclusive end of the right input run, fixed throughout `merge_lo`. -/
def mergeLoEndIndex (call : MergeAtCall κ ν) : Int :=
  call.ssb + Int.ofNat call.nb

/-- The post-initial-move traced continuation. -/
private def mergeLoTracedTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : TraceResult (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceedTraced? machine
  else if machine.na = 1 then
    mergeLoCopyBTraced? machine
  else
    mergeLoLoopTraced? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- Erased counterpart of `mergeLoTracedTail`. -/
private def mergeLoReferenceTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : Option (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceed? machine
  else if machine.na = 1 then
    mergeLoCopyB? machine
  else
    mergeLoLoop? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- The full continuation after the initial main-to-temporary bulk copy. -/
private def mergeLoTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeLoResult κ ν) :=
  (mergeLoCopyBIncrTraced? (mergeLoInitialMachine call state)).bind
    (mergeLoTracedTail call)

/-- Erased counterpart of `mergeLoTracedAfterCopy`. -/
private def mergeLoReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeLoResult κ ν) :=
  (mergeLoCopyBIncr? (mergeLoInitialMachine call state)).bind
    (mergeLoReferenceTail call)

/-- Output of the call-site/allocation/initial-copy stage.  It packages the
facts later stages actually consume, including the invariant of the exact
machine installed by the transcription. -/
structure MergeLoInitialStage
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.na call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
  copyPost : MainToTempMemcpyPost (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state copied
    0 call.ssa
  initialInvariant : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (mergeLoEndIndex call) (mergeLoInitialMachine call copied)

/-- Output of the initial `B` move plus the complete lockstep tail. -/
private structure MergeLoCoreStage (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (result : MergeLoResult κ ν) : Prop where
  corePost : MergeLoCorePost (mergeLoAllocated call).state call.na
    (mergeLoTracedAfterCopy call copied)
    (mergeLoReferenceAfterCopy call copied) result
  tempRead : (mergeLoTracedAfterCopy call copied).trace.HasTempAccess .read
