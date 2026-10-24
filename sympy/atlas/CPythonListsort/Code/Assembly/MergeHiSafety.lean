/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeTracePrimitives
import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemStorageValid
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety

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

/-! ## Provenance permits -/

/-- Provenance certificate consumed by the initial main-to-temporary copy. -/
theorem mergeHiInitialDataToTempPermit :
    (MergeMemcpySite.hi .initialDataToTemp).MainToTempPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

/-- Provenance certificate consumed by a galloping temporary-to-main copy. -/
theorem mergeHiGallopTempToDataPermit :
    (MergeMemcpySite.hi .gallopTempToData).TempToMainPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

/-- Provenance certificate consumed by the final temporary remainder copy. -/
theorem mergeHiFinalTempToDataPermit :
    (MergeMemcpySite.hi .finalTempToData).TempToMainPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

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

private def mergeHiGallopBFinishTraced? (afterB : MergeHiCursor κ ν)
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

private def mergeHiGallopBFinish? (afterB : MergeHiCursor κ ν)
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

private def mergeHiGallopBAfterTraced? (afterB : MergeHiCursor κ ν)
    (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if gallopB.fuelExhausted then
    mergeHiFuelExhaustedTraced afterB
  else
    let bCount := afterB.nb - gallopB.index
    (mergeHiMoveBBlockTraced? afterB bCount).bind fun movedB =>
      mergeHiGallopBFinishTraced? afterB aCount bCount movedB next

private def mergeHiGallopBAfter? (afterB : MergeHiCursor κ ν)
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

private def mergeHiGallopRoundFinishTraced? (movedA : MergeHiCursor κ ν)
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

private def mergeHiGallopRoundFinish? (movedA : MergeHiCursor κ ν)
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

private def mergeHiGallopRoundAfterTraced? (cursor : MergeHiCursor κ ν)
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

private def mergeHiGallopRoundAfter? (cursor : MergeHiCursor κ ν)
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
private def MergeHiMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

@[simp]
private theorem erase_mergeHiGallopBAfterTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat) (gallopB : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBAfterTraced? afterB aCount gallopB nextTraced).erase =
      mergeHiGallopBAfter? afterB aCount gallopB next := by
  unfold mergeHiGallopBAfterTraced? mergeHiGallopBAfter?
  cases hfuel : gallopB.fuelExhausted with
  | false =>
    change
      ((mergeHiMoveBBlockTraced? afterB
        (afterB.nb - gallopB.index)).bind fun movedB =>
          mergeHiGallopBFinishTraced? afterB aCount
            (afterB.nb - gallopB.index) movedB nextTraced).erase =
      (mergeHiMoveBBlock? afterB (afterB.nb - gallopB.index)).bind
        fun movedB => mergeHiGallopBFinish? afterB aCount
          (afterB.nb - gallopB.index) movedB next
    rw [TraceResult.erase_bind, erase_mergeHiMoveBBlockTraced]
    apply Option.bind_congr
    intro movedB _hmoved
    exact erase_mergeHiGallopBFinishTraced afterB aCount
      (afterB.nb - gallopB.index) movedB nextTraced next hnext
  | true =>
    change (mergeHiFuelExhaustedTraced afterB).erase =
      some (mergeHiFuelExhausted afterB)
    simp [mergeHiFuelExhaustedTraced]

private theorem mergeHiGallopB_eq_helpers
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopB? afterB aCount next =
      (afterB.state.data.read? afterB.ssa).bind fun left =>
        (initializedTempPrefix? afterB.state.a afterB.nb).bind fun temp =>
          mergeHiBindOptionAcross
              (gallopLeft? afterB.state temp 0 left.key afterB.nb
                (afterB.nb - 1))
              (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next) := by
  unfold mergeHiGallopB? mergeHiGallopBAfter?
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => simp [bind, Option.bind]
  | some left =>
    simp only [bind, Option.bind]
    cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
    | none => simp
    | some temp =>
      simp only [Bool.or_eq_true, BitVec.ofNat_eq_ofNat,
        Int.ofNat_eq_natCast]
      cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
        simp only [mergeHiBindOptionAcross]
        cases hfuel : gallop.fuelExhausted with
        | true =>
          have htrue : (true : Bool) = true := rfl
          rw [if_pos htrue, if_pos htrue]
        | false =>
          have hfalse : ¬ (false : Bool) = true := by decide
          rw [if_neg hfalse, if_neg hfalse]
          by_cases hcount : afterB.nb - gallop.index = 0
          · simp [Option.bind, hcount, mergeHiMoveBBlock?,
              mergeHiGallopBFinish?]
          · simp only [hcount, ↓reduceIte, mergeHiMoveBBlock?]
            cases hcopy : mergeHiMemcpyTempToData? .gallopTempToData rfl
                (afterB.nb - gallop.index) afterB.state
                (afterB.dest - Int.ofNat (afterB.nb - gallop.index) + 1)
                (afterB.ssb - Int.ofNat (afterB.nb - gallop.index) + 1) <;>
              simp [bind, Option.bind, mergeHiGallopBFinish?]

private theorem mergeHiGallopRound_eq_helpers
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopRound? cursor next =
      let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
      let state := { cursor.state with min_gallop := minGallop }
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key
            cursor.na (cursor.na - 1))
          (fun gallopA =>
            mergeHiGallopRoundAfter? cursor minGallop state gallopA next) := by
  simp only [mergeHiGallopRound?, mergeDataMemmove_eq,
    mergeTempRead_eq_mergeHiTempRead]
  cases hright : mergeHiTempRead?
      { cursor.state with
        min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.a
      cursor.ssb with
  | none => simp [bind, Option.bind]
  | some right =>
      simp only [bind, Option.bind]
      cases hgallop : gallopRight?
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.data
          cursor.basea right.key cursor.na (cursor.na - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
          simp only [mergeHiBindOptionAcross]
          cases hfuel : gallop.fuelExhausted with
          | true => simp [mergeHiGallopRoundAfter?, hfuel]
          | false =>
              simp only [mergeHiGallopRoundAfter?, hfuel, Bool.false_eq_true,
                ↓reduceIte]
              by_cases hcount : cursor.na - gallop.index = 0
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte,
                  mergeHiGallopRoundFinish?]
                rfl
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte]
                cases hmove : cursor.state.data.memmove?
                    (cursor.dest - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.ssa - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.na - gallop.index) with
                | none =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl
                | some data =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl

/-- Erasure commutes with the second half of one `merge_hi` galloping round
whenever it commutes with the supplied continuation. -/
private theorem erase_mergeHiGallopBTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      mergeHiGallopB? afterB aCount next := by
  rw [mergeHiGallopB_eq_helpers]
  unfold mergeHiGallopBTraced?
  rw [TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
  cases hLeft : afterB.state.data.read? afterB.ssa with
  | none => simp
  | some left =>
      simp only [Option.bind_some, TraceResult.erase_bind,
        erase_mergeHiTraceOption]
      cases hTemp : initializedTempPrefix? afterB.state.a afterB.nb with
      | none => simp
      | some temp =>
          simp only [Option.bind_some]
          rw [erase_mergeHiTemporaryGallopLeft_of_eq_some afterB.state
            afterB.nb (afterB.nb - 1) temp left.key hTemp]
          unfold mergeHiBindOptionAcross
          cases hGallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
              (afterB.nb - 1) with
          | none => simp
          | some gallop =>
              simp only [Option.bind_some]
              exact erase_mergeHiGallopBAfterTraced afterB aCount gallop
                nextTraced next hNext

private theorem erase_mergeHiGallopRoundFinishTraced
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced).erase =
      mergeHiGallopRoundFinish? movedA aCount next := by
  unfold mergeHiGallopRoundFinishTraced? mergeHiGallopRoundFinish?
  by_cases hFinished : movedA.na = 0
  · simp [hFinished, hNext]
  · rw [if_neg hFinished, if_neg hFinished, TraceResult.erase_bind,
      erase_mergeHiCopyTempDecrTraced]
    apply Option.bind_congr
    intro copiedB _hCopied
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    change
      (if afterB.nb = 1 then nextTraced afterB
        else mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      if afterB.nb = 1 then next afterB
        else mergeHiGallopB? afterB aCount next
    by_cases hOne : afterB.nb = 1
    · rw [if_pos hOne, if_pos hOne]
      exact hNext _
    · rw [if_neg hOne, if_neg hOne]
      exact erase_mergeHiGallopBTraced _ _ nextTraced next hNext

private theorem erase_mergeHiGallopRoundAfterTraced
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
      nextTraced).erase =
      mergeHiGallopRoundAfter? cursor minGallop state gallopA next := by
  unfold mergeHiGallopRoundAfterTraced? mergeHiGallopRoundAfter?
  cases hFuel : gallopA.fuelExhausted with
  | true => simp [erase_mergeHiFuelExhaustedTraced]
  | false =>
      simp only [Bool.false_eq_true, if_false, TraceResult.erase_bind,
        erase_mergeHiMoveABlockTraced]
      apply Option.bind_congr
      intro movedA _hMoved
      exact erase_mergeHiGallopRoundFinishTraced movedA
        (cursor.na - gallopA.index) nextTraced next hNext

/-- Erasure commutes with one complete `merge_hi` galloping round whenever it
commutes with the supplied continuation.  This premise-free structural bridge
is the proof-only API consumed by the top-level raw-domain erasure chain. -/
theorem erase_mergeHiGallopRoundTraced
    (cursor : MergeHiCursor κ ν)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundTraced? cursor nextTraced).erase =
      mergeHiGallopRound? cursor next := by
  rw [mergeHiGallopRound_eq_helpers]
  unfold mergeHiGallopRoundTraced?
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  change
    ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun right =>
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallopA =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
            nextTraced).erase =
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key cursor.na
            (cursor.na - 1)) fun gallopA =>
              mergeHiGallopRoundAfter? cursor minGallop state gallopA next
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hRight : mergeTempRead? state.a cursor.ssb with
  | none => simp
  | some right =>
      simp only [Option.bind_some, TraceResult.erase_bind]
      rw [erase_gallopRightTraced_main]
      unfold mergeHiBindOptionAcross
      cases hGallop : gallopRight? state state.data cursor.basea right.key
          cursor.na (cursor.na - 1) with
      | none => simp
      | some gallop =>
          simp only [Option.bind_some]
          exact erase_mergeHiGallopRoundAfterTraced cursor minGallop state
            gallop nextTraced next hNext

/-- State fields that the merge is forbidden to change.  Allocation may
change `a`, its backing, and `alloced`; the adaptive `min_gallop` is also an
intentional merge output. -/
structure MergeHiStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeHiStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_hi`.  The initial copy may replace payload
contents, so the frame records their extent rather than extensional equality. -/
structure MergeHiStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeHiStorageFrame

/-- Inductive invariant for every live right-to-left merge cursor.  The three
equalities are the subtraction-sensitive core: they retain the legal `-1`
sentinels rather than coercing backward cursors through `Nat`. -/
structure MergeHiCursorInvariant (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν) : Prop where
  baseNonnegative : 0 ≤ cursor.basea
  ssaEquation : cursor.ssa + 1 = cursor.basea + Int.ofNat cursor.na
  ssbEquation : cursor.ssb + 1 = Int.ofNat cursor.nb
  destEquation :
    cursor.dest + 1 = cursor.basea + Int.ofNat (cursor.na + cursor.nb)
  mainRange :
    cursor.basea + Int.ofNat (cursor.na + cursor.nb) ≤
      Int.ofNat cursor.state.data.entries.size
  leftWordBound : cursor.na ≤ PY_LIST_MAX
  rightWordBound : cursor.nb ≤ PY_LIST_MAX
  tempCapacity : cursor.nb ≤ cursor.state.a.cells.size
  tempValuesMode : TempRangeValuesMode cursor.state.a 0 cursor.nb
  tempInvariant : TempStorageInv cursor.state.a cursor.state.alloced
  tempLive : cursor.state.a.Live
  requestFits : request ≤ cursor.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant cursor.state.a.hasValues cursor.state.data
  stableFrame : MergeHiStableFrame origin cursor.state
  storageFrame : MergeHiStorageFrame origin cursor.state

/-- The outer fuel stays strictly ahead of the number of unmerged entries.
That one-step slack is created by the forced initial left copy. -/
def MergeHiFuelInvariant (fuel : Nat) (cursor : MergeHiCursor κ ν) : Prop :=
  cursor.na + cursor.nb < fuel

namespace MergeHiCursorInvariant

/-- Internal inductive postcondition shared by terminal paths and the phase
driver.  The reference computation is the corresponding reviewed untraced
fragment, so erasure stays lockstep throughout the induction. -/
private structure MergeHiCorePost
    (origin : MergeState κ ν) (request : Nat)
    (execution : TraceResult (MergeHiResult κ ν))
    (reference : Option (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  requestFits : request ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame origin result.state
  storageFrame : MergeHiStorageFrame origin result.state

private def MergeHiContinuationSafe
    (origin : MergeState κ ν) (request fuel : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) : Prop :=
  ∀ cursor,
    MergeHiCursorInvariant origin request cursor →
    MergeHiFuelInvariant fuel cursor →
    ∃ result, MergeHiCorePost origin request
      (nextTraced cursor) (next cursor) result

private theorem MergeHiCorePost.bind
    (origin : MergeState κ ν) (request : Nat)
    (current : TraceResult α)
    (next : α → TraceResult (MergeHiResult κ ν)) (value : α)
    (reference : Option (MergeHiResult κ ν)) (result : MergeHiResult κ ν)
    (hcurrent : current.result = some value)
    (hcurrentSafe : MovementTraceSafe current)
    (hnext : MergeHiCorePost origin request (next value) reference result)
    (herase : (current.bind next).erase = reference) :
    MergeHiCorePost origin request (current.bind next) reference result := by
  exact
    { resultEq := by
        unfold TraceResult.bind
        rw [hcurrent]
        exact hnext.resultEq
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafe := MovementTraceSafe.bind current next value hcurrent
        hcurrentSafe hnext.traceSafe
      exactErasure := herase
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      requestFits := hnext.requestFits
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

private theorem mergeHiGallopBTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request afterB)
    (hfuel : MergeHiFuelInvariant fuel afterB)
    (hna : 0 < afterB.na) (hnb : 1 < afterB.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopBTraced? afterB aCount nextTraced)
      (mergeHiGallopB? afterB aCount next) result := by
  have hssa := hinvariant.ssaInBounds hna
  rcases SortSlice.read_eq_some_of_indexInBounds afterB.state.data afterB.ssa
      hssa with ⟨left, hleft⟩
  have hleftResult :
      (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).result =
        some left := by
    change (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).erase =
      some left
    simpa using hleft
  have hleftSafe := mergeHiMainKeyReadTraced_safe afterB.state.data afterB.ssa
    hssa
  have hprefixInitialized : MergeHiTempPrefixInitialized afterB.state.a
      afterB.nb := by
    intro offset hoffset
    rcases hinvariant.tempValuesMode offset hoffset with
      ⟨entry, hread, _hmode⟩
    rw [erase_mergeTempRead] at hread
    refine ⟨entry, ?_⟩
    simpa [mergeTempRead_eq_mergeHiTempRead] using hread
  rcases mergeHiInitializedTempPrefix_exists_of_initialized afterB.state.a
      afterB.nb hprefixInitialized with ⟨temp, htemp⟩
  have htempResult :
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)).result = some temp := by
    rw [htemp]
    rfl
  have htempSafe : MovementTraceSafe
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)) := by
    simpa [mergeHiTraceOption, htemp] using MovementTraceSafe.pure temp
  have hagrees := initializedTempPrefix_agreesWithSlice_of_eq_some
    afterB.state.a afterB.nb temp htemp
  rcases gallopLeft_temporary_safe afterB.state afterB.state.a 0 temp 0
      left.key afterB.nb (afterB.nb - 1) hinvariant.temporaryValidRange
      hinvariant.tempLive hagrees (by omega) (by omega)
      hinvariant.rightWordBound with
    ⟨gallopB, hgallop, hgallopFuel, hgallopBound, htraceFuel,
      htracePushes, htraceBounds, htraceLive, hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)) :=
    ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  rcases mergeHiGallopBAfterTraced_safe origin request fuel afterB aCount
      gallopB hinvariant hfuel hna hgallopBound hgallopFuel nextTraced next
      hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
      left.key afterB.nb (afterB.nb - 1))
    (fun gallop => mergeHiGallopBAfterTraced? afterB aCount gallop
      nextTraced)
    (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next)
    gallopB result hgallop hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      (mergeHiBindOptionAcross
        (gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1))
        (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopLeft? afterB.state temp 0 left.key afterB.nb
      (afterB.nb - 1) <;> rfl
  have htempPost := MergeHiCorePost.prepend origin request
    (mergeHiTraceOption (initializedTempPrefix? afterB.state.a afterB.nb))
    (fun _temp =>
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun materialized => mergeHiBindOptionAcross
      (gallopLeft? afterB.state materialized 0 left.key afterB.nb
        (afterB.nb - 1))
      (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    temp result htempResult htempSafe hgallopPost'
  have htempPost' : MergeHiCorePost origin request
      ((mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      ((initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 left.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply htempPost.reference_eq
    rw [erase_mergeHiTraceOption]
  have hleftPost := MergeHiCorePost.prepend origin request
    (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa)
    (fun read =>
      (mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            read.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun read =>
      (initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 read.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    left result hleftResult hleftSafe htempPost'
  have hleftPost' := hleftPost.reference_eq
    (mergeHiGallopB_eq_helpers afterB aCount next).symm
  exact ⟨result, by
    simpa only [mergeHiGallopBTraced?, TraceResult.erase_sortSliceKeysRead]
      using hleftPost'⟩

private theorem mergeHiGallopRoundFinishTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request movedA)
    (hbudget : movedA.na + movedA.nb ≤ fuel)
    (hterminalFuel : movedA.na = 0 → MergeHiFuelInvariant fuel movedA)
    (hnb : 1 < movedA.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced)
      (mergeHiGallopRoundFinish? movedA aCount next) result := by
  by_cases hnaZero : movedA.na = 0
  · rcases hnext movedA hinvariant (hterminalFuel hnaZero) with
      ⟨result, hresult⟩
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero] using hresult⟩
  · have hna : 0 < movedA.na := Nat.pos_of_ne_zero hnaZero
    rcases mergeHiCopyTempDecrTraced_safe origin request movedA hinvariant
        (by omega) with
      ⟨copiedB, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    have hafterInv : MergeHiCursorInvariant origin request afterB := hcopiedInv
    have hafterFuel : MergeHiFuelInvariant fuel afterB := by
      change movedA.na + (movedA.nb - 1) < fuel
      omega
    let tracedTail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then nextTraced cursor
      else mergeHiGallopBTraced? cursor aCount nextTraced
    let tail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then next cursor
      else mergeHiGallopB? cursor aCount next
    have htail : ∃ result, MergeHiCorePost origin request
        (tracedTail copiedB) (tail copiedB) result := by
      by_cases hone : afterB.nb = 1
      · rcases hnext afterB hafterInv hafterFuel with ⟨result, hresult⟩
        have hone' : movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_pos hone', if_pos hone']
          exact hresult⟩
      · have hafterNa : 0 < afterB.na := by simpa [afterB] using hna
        have hafterNb : 1 < afterB.nb := by
          change 1 < movedA.nb - 1
          have hone' : ¬ movedA.nb - 1 = 1 := by
            simpa [afterB] using hone
          omega
        rcases mergeHiGallopBTraced_safe origin request fuel afterB aCount
            hafterInv hafterFuel hafterNa hafterNb nextTraced next hnext with
          ⟨result, hresult⟩
        have hone' : ¬ movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_neg hone', if_neg hone']
          exact hresult⟩
    rcases htail with ⟨result, htail⟩
    have hpost := MergeHiCorePost.prepend origin request
      (mergeHiCopyTempDecrTraced? movedA.state movedA.dest movedA.ssb)
      tracedTail tail copiedB result hcopy hcopySafe htail
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero, tracedTail, tail] using hpost⟩

private theorem mergeHiGallopRoundAfterTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (hinvariant : MergeHiCursorInvariant origin request
      { cursor with state := state, minGallop := minGallop })
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (hbound : gallopA.index ≤ cursor.na)
    (hnotFuel : gallopA.fuelExhausted = false)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA nextTraced)
      (mergeHiGallopRoundAfter? cursor minGallop state gallopA next) result := by
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  let aCount := cursor.na - gallopA.index
  have haCount : aCount ≤ adjusted.na := by
    simp [aCount, adjusted]
  rcases mergeHiMoveABlockTraced_safe origin request adjusted hinvariant
      aCount haCount with
    ⟨movedA, hmove, hmoveSafe, hmovedInv, hmovedNa, hmovedNb⟩
  have hmovedBudget : movedA.na + movedA.nb ≤ fuel := by
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    rw [hmovedNa, hmovedNb]
    simp only [adjusted]
    omega
  have hmovedTerminalFuel : movedA.na = 0 →
      MergeHiFuelInvariant fuel movedA := by
    intro hmovedZero
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    change movedA.na + movedA.nb < fuel
    rw [hmovedNa, hmovedNb]
    have hmovedZero' : adjusted.na - aCount = 0 := by
      rw [← hmovedNa]
      exact hmovedZero
    have hcursorZero : cursor.na - aCount = 0 := by
      simpa [adjusted] using hmovedZero'
    simp only [adjusted]
    have haPositive : 0 < aCount := by
      omega
    omega
  have hmovedNbPositive : 1 < movedA.nb := by
    simpa [hmovedNb, adjusted] using hnb
  rcases mergeHiGallopRoundFinishTraced_safe origin request fuel movedA aCount
      hmovedInv hmovedBudget hmovedTerminalFuel hmovedNbPositive nextTraced next
      hnext with ⟨result, hfinish⟩
  have hpost := MergeHiCorePost.prepend origin request
    (mergeHiMoveABlockTraced? adjusted aCount)
    (fun moved => mergeHiGallopRoundFinishTraced? moved aCount nextTraced)
    (fun moved => mergeHiGallopRoundFinish? moved aCount next)
    movedA result hmove hmoveSafe hfinish
  exact ⟨result, by
    simpa [mergeHiGallopRoundAfterTraced?, mergeHiGallopRoundAfter?,
      hnotFuel, adjusted, aCount] using hpost⟩

private theorem mergeHiGallopRoundTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundTraced? cursor nextTraced)
      (mergeHiGallopRound? cursor next) result := by
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  have hadjustedInv : MergeHiCursorInvariant origin request adjusted := by
    exact hinvariant.setMinGallop minGallop
  have hnbPositive : 0 < adjusted.nb := by
    simpa [adjusted] using Nat.zero_lt_of_lt hnb
  rcases hadjustedInv.tempReadable hnbPositive with ⟨right, hright⟩
  have hrightResult :
      (TraceResult.tempPayloadRead? state.a cursor.ssb).result = some right := by
    change (TraceResult.tempPayloadRead? state.a cursor.ssb).erase = some right
    rw [erase_mergeTempRead]
    simpa [adjusted, state] using hright
  have hrightSafe : MovementTraceSafe
      (TraceResult.tempPayloadRead? state.a cursor.ssb) := by
    apply mergeHiTempReadTraced_safe
    · simpa [adjusted, state] using hadjustedInv.ssbInBounds hnbPositive
    · simpa [adjusted, state] using hadjustedInv.tempLive
  have hvalid :
      (GallopKeySource.main state.data cursor.basea).ValidRange cursor.na := by
    simpa [adjusted, state] using hadjustedInv.mainValidRange
  rcases gallopRight_main_safe state state.data cursor.basea right.key
      cursor.na (cursor.na - 1) hvalid hna (by omega)
      hinvariant.leftWordBound with
    ⟨gallopA, hgallopResult, hgallopFuel, hgallopBound,
      hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive,
      hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)) :=
    ⟨hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive⟩
  rcases mergeHiGallopRoundAfterTraced_safe origin request fuel cursor
      minGallop state gallopA hadjustedInv hfuel hna hnb hgallopBound
      hgallopFuel nextTraced next hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopRightTraced? state (.main state.data cursor.basea) right.key
      cursor.na (cursor.na - 1))
    (fun gallop =>
      mergeHiGallopRoundAfterTraced? cursor minGallop state gallop nextTraced)
    (fun gallop =>
      mergeHiGallopRoundAfter? cursor minGallop state gallop next)
    gallopA result hgallopResult hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
      (mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea right.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopRight? state state.data cursor.basea right.key cursor.na
      (cursor.na - 1) <;> rfl
  have hrightPost := MergeHiCorePost.prepend origin request
    (TraceResult.tempPayloadRead? state.a cursor.ssb)
    (fun entry =>
      (gallopRightTraced? state (.main state.data cursor.basea) entry.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
    (fun entry =>
      mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea entry.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
    right result hrightResult hrightSafe hgallopPost'
  have hrightPost' : MergeHiCorePost origin request
      ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun entry =>
        (gallopRightTraced? state (.main state.data cursor.basea) entry.key
          cursor.na (cursor.na - 1)).bind fun gallop =>
            mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
              nextTraced)
      ((mergeTempRead? state.a cursor.ssb).bind fun entry =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea entry.key cursor.na
            (cursor.na - 1))
          (fun gallop =>
            mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hrightPost.reference_eq
    rw [erase_mergeTempRead]
  have hrightPost'' := hrightPost'.reference_eq
    (by simpa [minGallop, state] using
      (mergeHiGallopRound_eq_helpers cursor next).symm)
  exact ⟨result, by
    simpa only [mergeHiGallopRoundTraced?] using hrightPost''⟩

/-- Complete recursive driver contract.  The strict slack is consumed by one
real backward copy before each recursive call, while both terminal labels are
handled before phase dispatch. -/
private theorem mergeHiLoopTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant fuel cursor) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiLoopTraced? fuel cursor) (mergeHiLoop? fuel cursor) result := by
  induction fuel generalizing cursor with
  | zero =>
      unfold MergeHiFuelInvariant at hfuel
      omega
  | succ fuel ih =>
      by_cases hterminal : cursor.na = 0 ∨ cursor.nb = 0
      · simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal] using
          mergeHiSucceedTraced_safe origin request cursor hinvariant
      · have hna : 0 < cursor.na := by omega
        have hnbPositive : 0 < cursor.nb := by omega
        by_cases hnbOne : cursor.nb = 1
        · have hnaZero : ¬ cursor.na = 0 := by omega
          simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
            hnaZero] using
            mergeHiCopyATraced_safe origin request cursor hinvariant
              ⟨hnbOne, hna⟩
        · have hnb : 1 < cursor.nb := by omega
          cases hphase : cursor.phase with
          | galloping aCount bCount =>
              simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                hphase] using
                mergeHiGallopRoundTraced_safe origin request fuel cursor
                  hinvariant hfuel hna hnb (mergeHiLoopTraced? fuel)
                  (mergeHiLoop? fuel) ih
          | straight aCount bCount =>
              rcases hinvariant.tempReadable hnbPositive with
                ⟨right, hright⟩
              have hrightResult :
                  (TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).result = some right := by
                change (TraceResult.tempPayloadRead? cursor.state.a
                  cursor.ssb).erase = some right
                rw [erase_mergeTempRead]
                exact hright
              have hrightSafe := mergeHiTempReadTraced_safe cursor.state.a
                cursor.ssb (hinvariant.ssbInBounds hnbPositive)
                hinvariant.tempLive
              rcases SortSlice.read_eq_some_of_indexInBounds cursor.state.data
                  cursor.ssa (hinvariant.ssaInBounds hna) with
                ⟨left, hleft⟩
              have hleftResult :
                  (TraceResult.sortSliceKeysRead? cursor.state.data
                    cursor.ssa).result = some left := by
                change cursor.state.data.read? cursor.ssa = some left
                exact hleft
              have hleftSafe := mergeHiMainKeyReadTraced_safe
                cursor.state.data cursor.ssa (hinvariant.ssaInBounds hna)
              let tracedAfterLeft := fun (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
                else
                  (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
              let referenceAfterLeft := fun
                  (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecr? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
                else
                  (mergeHiCopyTempDecr? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
              have hselected : ∃ result, MergeHiCorePost origin request
                  (tracedAfterLeft right left)
                  (referenceAfterLeft right left) result := by
                by_cases hcompare :
                    cursor.state.key_compare right.key left.key = true
                · rcases mergeHiCopyDataDecrTraced_safe origin request cursor
                      hinvariant hna with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := aCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      na := cursor.na - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping nextCount 0
                        else
                          .straight nextCount 0
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping nextCount 0)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight nextCount 0)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                      cursor.ssa)
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyDataDecrTraced] using hcopyPost⟩
                · rcases mergeHiCopyTempDecrTraced_safe origin request cursor
                      hinvariant hnbPositive with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := bCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssb := copied.src
                      nb := cursor.nb - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping 0 nextCount
                        else
                          .straight 0 nextCount
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping 0 nextCount)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight 0 nextCount)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                      cursor.ssb)
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyTempDecrTraced] using hcopyPost⟩
              rcases hselected with ⟨result, hselected⟩
              have hleftPost := MergeHiCorePost.prepend origin request
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa)
                (tracedAfterLeft right) (referenceAfterLeft right) left result
                hleftResult
                hleftSafe hselected
              let tracedAfterRight := fun (entry : SortSliceEntry κ ν) =>
                (TraceResult.sortSliceKeysRead? cursor.state.data
                  cursor.ssa).bind (tracedAfterLeft entry)
              let referenceAfterRight := fun (entry : SortSliceEntry κ ν) =>
                cursor.state.data.read? cursor.ssa |>.bind
                  (referenceAfterLeft entry)
              have hleftPost' : MergeHiCorePost origin request
                  (tracedAfterRight right) (referenceAfterRight right) result := by
                simpa [tracedAfterRight, referenceAfterRight] using hleftPost
              have hrightPost := MergeHiCorePost.prepend origin request
                (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb)
                tracedAfterRight referenceAfterRight right result hrightResult
                hrightSafe hleftPost'
              have hrightPost' : MergeHiCorePost origin request
                  ((TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).bind tracedAfterRight)
                  ((mergeTempRead? cursor.state.a cursor.ssb).bind
                    referenceAfterRight) result := by
                apply hrightPost.reference_eq
                rw [erase_mergeTempRead]
              exact ⟨result, by
                simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                  hphase, tracedAfterRight, referenceAfterRight,
                  tracedAfterLeft, referenceAfterLeft,
                  mergeTempRead_eq_mergeHiTempRead]
                  using hrightPost'⟩

/-- The allocation performed at the `merge_hi` entry.  Naming it once keeps
the allocation/copy stage and later entry-erasure stage definitionally in
sync. -/
def mergeHiAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.nb)

/-- Full externally consumable postcondition for an actual `merge_at`
`merge_hi` continuation. -/
structure MergeHiSafetyPost
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  noMemoryEvents : execution.trace.memoryEvents = []
  exactErasure : execution.erase =
    mergeHi? call.state call.ssa call.ssb call.na call.nb
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : call.nb ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame call.state result.state
  geometry : MergeAtSafetyGeometry pre scanned i call
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  /-- Exact allocation certificate for the `merge_getmem` result consumed by
  the directional merge. -/
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  /-- Exact temporary-storage metadata frame from post-`merge_getmem` through
  the final right-to-left merge state. -/
  postGetmemStorageFrame :
    MergeHiStorageFrame (mergeHiAllocated call).state result.state
  /-- Reuse transports a caller-supplied physical-slot bound, while growth
  establishes it from the allocation guard. -/
  physicalSlotsBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent : execution.trace.HasAccess .read .inputKeys
  tempWriteEvent : execution.trace.HasTempAccess .write
  tempReadEvent : execution.trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    execution.trace.HasAccess .read .synchronizedValues

/-! ## Staged proof of the public contract -/

/-- Cursor immediately before CPython's forced first copy from the left run. -/
def mergeHiFullCursor (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : MergeHiCursor κ ν :=
  { state := copied
    dest := call.ssb + Int.ofNat (call.nb - 1)
    ssa := call.ssa + Int.ofNat (call.na - 1)
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na
    nb := call.nb
    minGallop := copied.min_gallop
    phase := .straight 0 0 }

/-- Cursor passed to the recursive phase machine after the forced first copy. -/
def mergeHiInitialCursor (call : MergeAtCall κ ν)
    (forced : MergeHiDataCursorResult κ ν) : MergeHiCursor κ ν :=
  { state := forced.state
    dest := forced.dst
    ssa := forced.src
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na - 1
    nb := call.nb
    minGallop := forced.state.min_gallop
    phase := .straight 0 0 }

/-- Traced continuation following the forced first copy. -/
private def mergeHiTracedTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : TraceResult (MergeHiResult κ ν) :=
  mergeHiLoopTraced? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Reviewed untraced continuation corresponding to `mergeHiTracedTail`. -/
private def mergeHiReferenceTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : Option (MergeHiResult κ ν) :=
  mergeHiLoop? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Traced entry continuation following the initial main-to-temporary copy. -/
private def mergeHiTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecrTraced? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiTracedTail call)

/-- Untraced entry continuation corresponding to `mergeHiTracedAfterCopy`. -/
private def mergeHiReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecr? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiReferenceTail call)

/-- Evidence produced by the call-site/allocation stage.  It fixes the exact
initial `memcpy`, the forced first backward copy, and the cursor invariant that
the recursive phase machine consumes. -/
structure MergeHiPrepared
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  allocation : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  initialCopy : MainToTempMemcpyPost (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit call.nb (mergeHiAllocated call).state copied
    0 call.ssb
  forcedResult :
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1))).result = some forced
  forcedSafe : MovementTraceSafe
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
  initialInvariant : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
    (mergeHiInitialCursor call forced)
  initialFuel : MergeHiFuelInvariant (call.na + call.nb)
    (mergeHiInitialCursor call forced)

/-- Lockstep result after the recursive merge driver has finished.  Besides
the aggregate core contract, this stage retains the exact traced entry shape
and the non-vacuous temporary-read witness needed by the observable post. -/
private structure MergeHiLockstepPost
    (call : MergeAtCall κ ν) (copied : MergeState κ ν)
    (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  tracedEntry :
    mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb).bind
          (mergeHiTracedAfterCopy call)
  afterCopyRead :
    (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read

/-- The loop/lockstep stage consumes only the prepared cursor contract.  It
proves termination, exact erasure against the untraced transcription, and a
real temporary read on every successful path. -/
private theorem mergeHi_lockstep
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν)
    (hprepared : MergeHiPrepared pre scanned i call copied forced) :
    ∃ result, MergeHiLockstepPost call copied result := by
  have hgeometry := hprepared.geometry
  have hallocPost := hprepared.allocation
  have hcopy := hprepared.initialCopy
  have hinitial := hprepared.initialInvariant
  rcases mergeHiLoopTraced_safe (mergeHiAllocated call).state call.nb
      (call.na + call.nb)
      (mergeHiInitialCursor call forced) hinitial hprepared.initialFuel with
    ⟨result, hloop⟩
  have hsumPositive : 0 < call.na + call.nb := by
    have hna := hgeometry.leftPositive
    omega
  let loopFuel := call.na + call.nb - 1
  have hloopFuelEq : call.na + call.nb = loopFuel + 1 := by
    dsimp [loopFuel]
    omega
  have hloopRead :
      (mergeHiLoopTraced? (call.na + call.nb)
        (mergeHiInitialCursor call forced)).trace.HasTempAccess .read := by
    by_cases hnaZero : (mergeHiInitialCursor call forced).na = 0
    · have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
        simpa [mergeHiInitialCursor] using hgeometry.rightPositive
      rw [hloopFuelEq]
      simpa [mergeHiLoopTraced?, hnaZero] using
        mergeHiSucceedTraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial hnbPositive
    · have hnaPositive : 0 < (mergeHiInitialCursor call forced).na :=
        Nat.pos_of_ne_zero hnaZero
      by_cases hnbOne : (mergeHiInitialCursor call forced).nb = 1
      · have hterminal : ¬ ((mergeHiInitialCursor call forced).na = 0 ∨
            (mergeHiInitialCursor call forced).nb = 0) := by
          omega
        rw [hloopFuelEq, mergeHiLoopTraced?, if_neg hterminal,
          if_pos hnbOne]
        exact mergeHiCopyATraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial ⟨hnbOne, hnaPositive⟩
      · have hnbLarge : 1 < (mergeHiInitialCursor call forced).nb := by
          have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
            simpa [mergeHiInitialCursor] using hgeometry.rightPositive
          omega
        rw [hloopFuelEq]
        exact mergeHiInitialLoop_hasTempRead loopFuel
          (mergeHiInitialCursor call forced) hnaPositive hnbLarge (by rfl)
  have hloop' : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedTail call forced) (mergeHiReferenceTail call forced)
      result := by
    simpa [mergeHiTracedTail, mergeHiReferenceTail] using hloop
  have hafterForced := MergeHiCorePost.prepend
    (mergeHiAllocated call).state call.nb
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
    (mergeHiTracedTail call) (mergeHiReferenceTail call) forced result
    hprepared.forcedResult hprepared.forcedSafe hloop'
  have hafterCopy : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedAfterCopy call copied)
      (mergeHiReferenceAfterCopy call copied) result := by
    simpa [mergeHiTracedAfterCopy, mergeHiReferenceAfterCopy,
      erase_mergeHiCopyDataDecrTraced] using hafterForced
  have hafterCopyRead :
      (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read := by
    apply mergeHiHasTempAccess_bind_right
      (mergeHiCopyDataDecrTraced? copied
        (call.ssb + Int.ofNat (call.nb - 1))
        (call.ssa + Int.ofNat (call.na - 1)))
      (mergeHiTracedTail call) forced .read hprepared.forcedResult
    simpa [mergeHiTracedTail] using hloopRead
  have hwhole := MergeHiCorePost.prepend (mergeHiAllocated call).state call.nb
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb
      (mergeHiAllocated call).state 0 call.ssb)
    (mergeHiTracedAfterCopy call) (mergeHiReferenceAfterCopy call) copied
    result hcopy.success hcopy.traceSafe hafterCopy
  have hreference :
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).erase.bind
            (mergeHiReferenceAfterCopy call) =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    calc
      _ = (mainToTempMemcpy? call.nb (mergeHiAllocated call).state 0
          call.ssb).bind (mergeHiReferenceAfterCopy call) := congrArg
            (fun option => option.bind (mergeHiReferenceAfterCopy call))
            hcopy.exactErasure
      _ = _ := congrArg
        (fun option => option.bind (mergeHiReferenceAfterCopy call))
        (mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp .initialDataToTemp rfl
          call.nb (mergeHiAllocated call).state 0 call.ssb)
  have hwholeTagged := MergeHiCorePost.reference_eq hwhole hreference
  have hentryGuard :
      0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
        call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨hgeometry.leftPositive, hgeometry.rightPositive,
      hgeometry.leftWordBound, hgeometry.rightWordBound, hgeometry.adjacent⟩
  have htracedEntry :
      mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
        (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiTracedAfterCopy call) := by
    rw [mergeHiTraced?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hreferenceEntry :
      mergeHi? call.state call.ssa call.ssb call.na call.nb =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    rw [mergeHi?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hcore : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
      (mergeHi? call.state call.ssa call.ssb call.na call.nb) result := by
    rw [htracedEntry, hreferenceEntry]
    exact hwholeTagged
  exact ⟨result,
    { core := hcore
      tracedEntry := htracedEntry
      afterCopyRead := hafterCopyRead }⟩

/-- Observable evidence separated from the recursive lockstep proof.  These
witnesses rule out a vacuous safety result: the successful merge really reads
the input, writes and later reads temporary storage, and preserves the
classified-`memcpy` provenance boundary. -/
private structure MergeHiObservablePost
    (call : MergeAtCall κ ν) (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .inputKeys
  tempWriteEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .write
  tempReadEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .synchronizedValues

/-- Safety of the concrete `merge_hi` continuation selected by `merge_at`.
All cursor geometry, allocation admissibility, positivity, word bounds, and
backward-sentinel arithmetic are derived from the pending layout and the
actual preparation equation. -/
theorem mergeHi_safe
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result, MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  rcases mergeHi_prepare pre scanned i call hlayout hmax hprepare hInv hLive
      hMode with ⟨copied, forced, hprepared⟩
  rcases mergeHi_lockstep pre scanned i call copied forced hprepared with
    ⟨result, hlockstep⟩
  have hobservable := mergeHi_observables pre scanned i call copied forced
    result hprepared hlockstep
  have hcore := hobservable.core
  have hlogical := TempStorageInv.cells_size_eq hcore.tempInvariant
    hcore.tempLive
  have hphysicalBound :
      call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
        result.state.a.physicalSlots ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    intro hbefore
    rw [hcore.storageFrame.physicalSlots_eq]
    rcases hprepared.allocation.outcome with hreuse | hgrown
    · rw [hprepared.allocation.reuseAccounting hreuse]
      exact hbefore
    · exact (hprepared.allocation.growthAccounting hgrown).2.2.2.2
  exact ⟨result,
    { resultEq := hcore.resultEq
      returnCode := hcore.returnCode
      resultFuel := hcore.resultFuel
      traceFuel := hcore.traceSafe.fuel
      accessesInBounds := hcore.traceSafe.bounds
      tempAccessesLive := hcore.traceSafe.tempLive
      noPushes := hcore.traceSafe.noPushes
      noMemoryEvents := mergeHiTraced_memoryEvents_empty
        call.state call.ssa call.ssb call.na call.nb
      exactErasure := hcore.exactErasure
      tempInvariant := hcore.tempInvariant
      tempLive := hcore.tempLive
      logicalCapacity := hlogical
      requestFits := hcore.requestFits
      valuesMode := hcore.valuesMode
      stableFrame := (MergeHiStableFrame.of_getmem call.state
        (BitVec.ofNat 64 call.nb) hprepared.allocation).trans hcore.stableFrame
      geometry := hprepared.geometry
      requestFacts := hprepared.requestFacts
      inputTempInvariant := hprepared.inputTempInvariant
      inputTempLive := hprepared.inputTempLive
      inputValuesMode := hprepared.inputValuesMode
      directionalDispatch := hprepared.directionalDispatch
      allocationPost := hprepared.allocation
      postGetmemStorageFrame := hcore.storageFrame
      physicalSlotsBound := hphysicalBound
      memcpyProvenance := hobservable.memcpyProvenance
      inputKeyEvent := hobservable.inputKeyEvent
      tempWriteEvent := hobservable.tempWriteEvent
      tempReadEvent := hobservable.tempReadEvent
      synchronizedValuesEvent := hobservable.synchronizedValuesEvent }⟩
end CPythonListsort
