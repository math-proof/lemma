/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Transcription.MergeHi.Part3
/-!
# Right-to-left stable merge transcription

This module transcribes CPython's `merge_hi` from the pinned
`Objects/listobject.c`.  The active list remains in `MergeState.data`; the
shorter right run is copied into `MergeState.a`, whose optional cells retain
the distinction between allocated and initialized temporary storage.

The ordinary and galloping loops are represented by a fuel-bounded phase
machine.  Modeled assertion or bounds failures return `none`.  Exhaustion of
the explicit loop or of a nested gallop is instead observable through
`fuelExhausted`, while rejection by `merge_getmem` retains C's `-1` result.

Equality selects B while filling backward, leaving the equal A entry before it
in final forward order.  Galloping retains C's `na == 0` and `nb == 0` branches
for inconsistent but total comparators, including the `na - k` and `nb - k`
conversions from insertion indices to backward block lengths.

Version one has no comparator-error result.  CPython's comparator-error jumps
to `Fail` are deliberately absent, while the temp-to-data copyback shared by
C's `Succeed` and `Fail` labels remains on successful exits.  Distinct
temp/data block copies model `sortslice_memcpy`; blocks moved within `data` use
overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

def mergeHiCountAtLeast (count : Nat) (threshold : PySSize) : Bool :=
  !((BitVec.ofNat 64 count).slt threshold)

/-- `min_gallop -= min_gallop > 1`, with the signed comparison used by C. -/
def mergeHiDecreaseMinGallop (minGallop : PySSize) : PySSize :=
  if (1 : PySSize).slt minGallop then minGallop - 1 else minGallop

def mergeHiFuelExhausted (cursor : MergeHiCursor κ ν) :
    MergeHiResult κ ν :=
  { state := cursor.state, returnCode := -1, fuelExhausted := true }

/-- The remainder copy shared by C's `Succeed` and `Fail` labels.  Comparator
errors are outside the total Boolean comparator model, so only the successful
entry is retained here; the modeled pre-loop allocation guard has its own
negative result. -/
def mergeHiSucceed? (cursor : MergeHiCursor κ ν) :
    Option (MergeHiResult κ ν) := do
  let state ←
    if cursor.nb = 0 then
      some cursor.state
    else
      mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb cursor.state
        (cursor.dest - Int.ofNat (cursor.nb - 1)) 0
  pure { state := state, returnCode := 0, fuelExhausted := false }

/-- The `CopyA` tail, reached with the single smallest right-run element still
in temporary storage. -/
def mergeHiCopyA? (cursor : MergeHiCursor κ ν) :
    Option (MergeHiResult κ ν) := do
  if cursor.nb = 1 ∧ 0 < cursor.na then
    let offset := 1 - Int.ofNat cursor.na
    let data ← mergeDataMemmove? .hiCopyATail cursor.state.data
      (cursor.dest + offset) (cursor.ssa + offset) cursor.na
    let state := { cursor.state with data := data }
    let state ← mergeHiCopyTempToData? state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb
    pure { state := state, returnCode := 0, fuelExhausted := false }
  else
    none

/-- The second half of one `merge_hi` galloping round, parameterized by the
recursive continuation so its structural frame can be proved independently. -/
def mergeHiGallopB? (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) := do
  let left ← afterB.state.data.read? afterB.ssa
  let temp ← initializedTempPrefix? afterB.state.a afterB.nb
  mergeHiBindOptionAcross
      (gallopLeft? afterB.state temp 0 left.key
        afterB.nb (afterB.nb - 1)) fun gallopB =>
    if gallopB.fuelExhausted then
      some (mergeHiFuelExhausted afterB)
    else do
      -- C's `k = nb - k`: backward merging consumes the suffix beginning at
      -- `gallop_left`'s insertion point.
      let bCount := afterB.nb - gallopB.index
      let movedB ←
        if bCount = 0 then
          some afterB
        else do
          let dest := afterB.dest - Int.ofNat bCount
          let ssb := afterB.ssb - Int.ofNat bCount
          let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl
            bCount afterB.state
            (dest + 1) (ssb + 1)
          some
            { afterB with
              state := state
              dest := dest
              ssb := ssb
              nb := afterB.nb - bCount }
      -- Preserve C's inconsistent-comparator `nb == 0` hedge; the common
      -- dispatcher distinguishes it from CopyA.
      if movedB.nb = 0 ∨ movedB.nb = 1 then
        next movedB
      else
        let copiedA ← mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa
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

/-- One complete `merge_hi` galloping round, parameterized by the recursive
continuation. -/
def mergeHiGallopRound? (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) := do
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state := { cursor.state with min_gallop := minGallop }
  let right ← mergeHiTempRead? state.a cursor.ssb
  mergeHiBindOptionAcross
      (gallopRight? state state.data cursor.basea right.key
        cursor.na (cursor.na - 1)) fun gallopA =>
    if gallopA.fuelExhausted then
      some (mergeHiFuelExhausted { cursor with state := state })
    else do
      -- C's `k = na - k`: backward merging consumes the suffix after the
      -- insertion point returned by `gallop_right`.
      let aCount := cursor.na - gallopA.index
      let movedA ←
        if aCount = 0 then
          some { cursor with state := state, minGallop := minGallop }
        else do
          let dest := cursor.dest - Int.ofNat aCount
          let ssa := cursor.ssa - Int.ofNat aCount
          let data ← mergeDataMemmove? .hiGallopA state.data
            (dest + 1) (ssa + 1) aCount
          some
            { cursor with
              state := { state with data := data }
              dest := dest
              ssa := ssa
              na := cursor.na - aCount
              minGallop := minGallop }
      if movedA.na = 0 then
        next movedA
      else
        let copiedB ← mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb
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

def mergeHiLoop? :
    Nat → MergeHiCursor κ ν → Option (MergeHiResult κ ν)
  | 0, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceed? cursor
      else if cursor.nb = 1 then
        mergeHiCopyA? cursor
      else
        some (mergeHiFuelExhausted cursor)
  | fuel + 1, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceed? cursor
      else if cursor.nb = 1 then
        mergeHiCopyA? cursor
      else
        match cursor.phase with
        | .straight aCount bCount => do
            let right ← mergeHiTempRead? cursor.state.a cursor.ssb
            let left ← cursor.state.data.read? cursor.ssa
            if iflt cursor.state.key_compare right.key left.key then
              let copied ← mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa
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
              mergeHiLoop? fuel next
            else
              let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb
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
              mergeHiLoop? fuel next
        | .galloping _ _ =>
            mergeHiGallopRound? cursor (mergeHiLoop? fuel)

/-- Transcription of CPython's right-to-left stable merge.

`ssa` and `ssb` are signed base indices into `state.data`; `na` and `nb` are
their positive, signed-`Py_ssize_t`-representable lengths.  Adjacency is an
assertion-domain check.  No `na ≥ nb` check is added because the pinned C
routine documents that selection condition but does not assert it locally.
-/
def mergeHi? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    Option (MergeHiResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    match allocated.outcome with
    | .guardRejected =>
        some
          { state := allocated.state
            returnCode := -1
            fuelExhausted := false }
    | .reused | .grown => do
        let state ← mergeHiMemcpyDataToTemp? .initialDataToTemp rfl
          nb allocated.state 0 ssb
        let dest := ssb + Int.ofNat (nb - 1)
        let ssaCursor := ssa + Int.ofNat (na - 1)
        let copied ← mergeHiCopyDataDecr? state dest ssaCursor
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
        mergeHiLoop? (na + nb) cursor
  else
    none

end CPythonListsort
