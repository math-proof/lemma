/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Theorem.CPythonListsort.Code.Assembly.MergeLoSafety
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
def MergeLoMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

end CPythonListsort
