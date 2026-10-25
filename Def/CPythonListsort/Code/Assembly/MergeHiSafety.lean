/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Traced atomic merge operations -/

/-- Lift the reviewed, access-free prefix materializer into the trace monad.
The resulting slice is a semantic bridge only: gallop accesses still target
the physical temporary backing below. -/
def mergeHiTraceOption : Option α → TraceResult α
  | none => TraceResult.failure
  | some value => TraceResult.pure value

/-- One overlap-safe main-data copy followed by decrementing both cursors. -/
def mergeHiCopyDataDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  mainDataCopyDecrTraced? state dst src

/-- One temporary-to-main copy followed by decrementing both cursors. -/
def mergeHiCopyTempDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  (tempToMainCellTraced? state dst src).map fun copied =>
    { state := copied, dst := dst - 1, src := src - 1 }

/-- Consume a suffix of the active left run with overlap-safe main movement. -/
def mergeHiMoveABlockTraced? (cursor : MergeHiCursor κ ν) (count : Nat) :
    TraceResult (MergeHiCursor κ ν) :=
  if count = 0 then
    TraceResult.pure cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssa := cursor.ssa - Int.ofNat count
    (mainDataMemmoveTraced? cursor.state (dest + 1) (ssa + 1) count).map
      fun state =>
        { cursor with
          state := state
          dest := dest
          ssa := ssa
          na := cursor.na - count }

/-- Consume a suffix of the active temporary right run.  The tagged permit is
part of the operation, so no same-backing `memcpy` interpretation is possible. -/
def mergeHiMoveBBlockTraced? (cursor : MergeHiCursor κ ν) (count : Nat) :
    TraceResult (MergeHiCursor κ ν) :=
  if count = 0 then
    TraceResult.pure cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssb := cursor.ssb - Int.ofNat count
    (tempToMainMemcpyTraced? (.hi .gallopTempToData)
      mergeHiGallopTempToDataPermit count cursor.state
      (dest + 1) (ssb + 1)).map fun state =>
        { cursor with
          state := state
          dest := dest
          ssb := ssb
          nb := cursor.nb - count }

def mergeHiMoveABlock? (cursor : MergeHiCursor κ ν) (count : Nat) :
    Option (MergeHiCursor κ ν) :=
  if count = 0 then
    some cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssa := cursor.ssa - Int.ofNat count
    do
      let state ← mainDataMemmove? cursor.state (dest + 1) (ssa + 1) count
      some
        { cursor with
          state := state
          dest := dest
          ssa := ssa
          na := cursor.na - count }

def mergeHiMoveBBlock? (cursor : MergeHiCursor κ ν) (count : Nat) :
    Option (MergeHiCursor κ ν) :=
  if count = 0 then
    some cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssb := cursor.ssb - Int.ofNat count
    do
      let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl count
        cursor.state (dest + 1) (ssb + 1)
      some
        { cursor with
          state := state
          dest := dest
          ssb := ssb
          nb := cursor.nb - count }

/-- Observable merge-fuel exhaustion also marks trace fuel exhaustion. -/
def mergeHiFuelExhaustedTraced (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  (TraceResult.pure (mergeHiFuelExhausted cursor)).markFuelExhausted

/-- The successful remainder-copy tail shared by the C `Succeed` and `Fail`
labels. -/
def mergeHiSucceedTraced? (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  let copied :=
    if cursor.nb = 0 then
      TraceResult.pure cursor.state
    else
      tempToMainMemcpyTraced? (.hi .finalTempToData)
        mergeHiFinalTempToDataPermit cursor.nb cursor.state
        (cursor.dest - Int.ofNat (cursor.nb - 1)) 0
  copied.map fun state =>
    { state := state, returnCode := 0, fuelExhausted := false }

/-- The `CopyA` tail with one temporary right-run entry remaining. -/
def mergeHiCopyATraced? (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  if cursor.nb = 1 ∧ 0 < cursor.na then
    let offset := 1 - Int.ofNat cursor.na
    (mainDataMemmoveTraced? cursor.state
      (cursor.dest + offset) (cursor.ssa + offset) cursor.na).bind fun state =>
        (tempToMainCellTraced? state
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb).map fun state =>
            { state := state, returnCode := 0, fuelExhausted := false }
  else
    TraceResult.failure

/-! ## Traced galloping and driver -/

def mergeHiGallopBFinishTraced? (afterB : MergeHiCursor κ ν)
    (aCount bCount : Nat) (movedB : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if movedB.nb = 0 ∨ movedB.nb = 1 then
    next movedB
  else
    (mergeHiCopyDataDecrTraced? movedB.state movedB.dest
      movedB.ssa).bind fun copiedA =>
        let afterA : MergeHiCursor κ ν :=
          { movedB with
            state := copiedA.state
            dest := copiedA.dst
            ssa := copiedA.src
            na := movedB.na - 1 }
        if afterA.na = 0 then
          next afterA
        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
            mergeHiCountAtLeast bCount MIN_GALLOP then
          next { afterA with phase := .galloping aCount bCount }
        else
          let minGallop := afterB.minGallop + 1
          let state := { afterA.state with min_gallop := minGallop }
          next
            { afterA with
              state := state
              minGallop := minGallop
              phase := .straight 0 0 }

def mergeHiGallopBFinish? (afterB : MergeHiCursor κ ν)
    (aCount bCount : Nat) (movedB : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if movedB.nb = 0 ∨ movedB.nb = 1 then
    next movedB
  else
    (mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa).bind
      fun copiedA =>
        let afterA : MergeHiCursor κ ν :=
          { movedB with
            state := copiedA.state
            dest := copiedA.dst
            ssa := copiedA.src
            na := movedB.na - 1 }
        if afterA.na = 0 then
          next afterA
        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
            mergeHiCountAtLeast bCount MIN_GALLOP then
          next { afterA with phase := .galloping aCount bCount }
        else
          let minGallop := afterB.minGallop + 1
          let state := { afterA.state with min_gallop := minGallop }
          next
            { afterA with
              state := state
              minGallop := minGallop
              phase := .straight 0 0 }

def mergeHiGallopBAfterTraced? (afterB : MergeHiCursor κ ν)
    (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if gallopB.fuelExhausted then
    mergeHiFuelExhaustedTraced afterB
  else
    let bCount := afterB.nb - gallopB.index
    (mergeHiMoveBBlockTraced? afterB bCount).bind fun movedB =>
      mergeHiGallopBFinishTraced? afterB aCount bCount movedB next

def mergeHiGallopBAfter? (afterB : MergeHiCursor κ ν)
    (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if gallopB.fuelExhausted then
    some (mergeHiFuelExhausted afterB)
  else
    let bCount := afterB.nb - gallopB.index
    (mergeHiMoveBBlock? afterB bCount).bind fun movedB =>
      mergeHiGallopBFinish? afterB aCount bCount movedB next

/-- Second half of a `merge_hi` galloping round.  The temporary gallop uses
the real temporary backing directly; no synthetic `SortSlice` access is
recorded. -/
def mergeHiGallopBTraced? (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).bind fun left =>
    (mergeHiTraceOption
      (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
      (gallopLeftTraced? afterB.state
        (.temporary afterB.state.a 0) left.key afterB.nb
        (afterB.nb - 1)).bind fun gallopB =>
        mergeHiGallopBAfterTraced? afterB aCount gallopB next

def mergeHiGallopRoundFinishTraced? (movedA : MergeHiCursor κ ν)
    (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if movedA.na = 0 then
    next movedA
  else
    (mergeHiCopyTempDecrTraced? movedA.state movedA.dest movedA.ssb).bind
      fun copiedB =>
        let afterB : MergeHiCursor κ ν :=
          { movedA with
            state := copiedB.state
            dest := copiedB.dst
            ssb := copiedB.src
            nb := movedA.nb - 1 }
        if afterB.nb = 1 then
          next afterB
        else
          mergeHiGallopBTraced? afterB aCount next

def mergeHiGallopRoundFinish? (movedA : MergeHiCursor κ ν)
    (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if movedA.na = 0 then
    next movedA
  else
    (mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb).bind
      fun copiedB =>
        let afterB : MergeHiCursor κ ν :=
          { movedA with
            state := copiedB.state
            dest := copiedB.dst
            ssb := copiedB.src
            nb := movedA.nb - 1 }
        if afterB.nb = 1 then
          next afterB
        else
          mergeHiGallopB? afterB aCount next

def mergeHiGallopRoundAfterTraced? (cursor : MergeHiCursor κ ν)
    (minGallop : PySSize) (state : MergeState κ ν) (gallopA : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if gallopA.fuelExhausted then
    mergeHiFuelExhaustedTraced { cursor with state := state }
  else
    let aCount := cursor.na - gallopA.index
    (mergeHiMoveABlockTraced?
      { cursor with state := state, minGallop := minGallop } aCount).bind
      fun movedA => mergeHiGallopRoundFinishTraced? movedA aCount next

def mergeHiGallopRoundAfter? (cursor : MergeHiCursor κ ν)
    (minGallop : PySSize) (state : MergeState κ ν) (gallopA : GallopResult)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if gallopA.fuelExhausted then
    some (mergeHiFuelExhausted { cursor with state := state })
  else
    let aCount := cursor.na - gallopA.index
    (mergeHiMoveABlock?
      { cursor with state := state, minGallop := minGallop } aCount).bind
      fun movedA => mergeHiGallopRoundFinish? movedA aCount next

/-- One complete traced `merge_hi` galloping round. -/
def mergeHiGallopRoundTraced? (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state := { cursor.state with min_gallop := minGallop }
  (TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun right =>
    (gallopRightTraced? state (.main state.data cursor.basea) right.key
      cursor.na (cursor.na - 1)).bind fun gallopA =>
        mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA next

/-- Fuel-bounded traced phase machine.  A live nonterminal zero-fuel state
marks trace exhaustion instead of returning an access-free failure. -/
def mergeHiLoopTraced? :
    Nat → MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)
  | 0, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceedTraced? cursor
      else if cursor.nb = 1 then
        mergeHiCopyATraced? cursor
      else
        mergeHiFuelExhaustedTraced cursor
  | fuel + 1, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceedTraced? cursor
      else if cursor.nb = 1 then
        mergeHiCopyATraced? cursor
      else
        match cursor.phase with
        | .straight aCount bCount =>
            (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb).bind
              fun right =>
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa).bind
                  fun left =>
                    if iflt cursor.state.key_compare right.key left.key then
                      (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                        cursor.ssa).bind fun copied =>
                          let aCount := aCount + 1
                          let next : MergeHiCursor κ ν :=
                            { cursor with
                              state := copied.state
                              dest := copied.dst
                              ssa := copied.src
                              na := cursor.na - 1
                              phase :=
                                if mergeHiCountAtLeast aCount cursor.minGallop then
                                  .galloping aCount 0
                                else
                                  .straight aCount 0
                              minGallop :=
                                if mergeHiCountAtLeast aCount cursor.minGallop then
                                  cursor.minGallop + 1
                                else
                                  cursor.minGallop }
                          mergeHiLoopTraced? fuel next
                    else
                      (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                        cursor.ssb).bind fun copied =>
                          let bCount := bCount + 1
                          let next : MergeHiCursor κ ν :=
                            { cursor with
                              state := copied.state
                              dest := copied.dst
                              ssb := copied.src
                              nb := cursor.nb - 1
                              phase :=
                                if mergeHiCountAtLeast bCount cursor.minGallop then
                                  .galloping 0 bCount
                                else
                                  .straight 0 bCount
                              minGallop :=
                                if mergeHiCountAtLeast bCount cursor.minGallop then
                                  cursor.minGallop + 1
                                else
                                  cursor.minGallop }
                          mergeHiLoopTraced? fuel next
        | .galloping _ _ =>
            mergeHiGallopRoundTraced? cursor (mergeHiLoopTraced? fuel)

/-! ## Public evaluator -/

/-- Directly traced transcription of CPython's right-to-left merge. -/
def mergeHiTraced? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    TraceResult (MergeHiResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    match allocated.outcome with
    | .guardRejected =>
        TraceResult.pure
          { state := allocated.state
            returnCode := -1
            fuelExhausted := false }
    | .reused | .grown =>
        (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit nb allocated.state 0 ssb).bind fun state =>
            let dest := ssb + Int.ofNat (nb - 1)
            let ssaCursor := ssa + Int.ofNat (na - 1)
            (mergeHiCopyDataDecrTraced? state dest ssaCursor).bind fun copied =>
              let cursor : MergeHiCursor κ ν :=
                { state := copied.state
                  dest := copied.dst
                  ssa := copied.src
                  ssb := Int.ofNat (nb - 1)
                  basea := ssa
                  na := na - 1
                  nb := nb
                  minGallop := copied.state.min_gallop
                  phase := .straight 0 0 }
              mergeHiLoopTraced? (na + nb) cursor
  else
    TraceResult.failure

/-! ## Absence of nested merge-memory and policy events -/

/-- A local trace fragment contains neither a top-level merge-memory boundary
nor a merge-policy event.  The shared structural induction below pins both
absence claims. -/
def MergeHiMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

end CPythonListsort
