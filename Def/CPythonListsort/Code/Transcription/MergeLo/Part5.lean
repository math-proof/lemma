/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Inductive.CPythonListsort.Code.Transcription.MergeLo.Part2
/-!
# Left-to-right merge transcription

This module transcribes CPython's `merge_lo`.  The main list remains in
`MergeState.data`; the shorter left run is copied into `MergeState.a` before
the merge starts.  Invalid assertion inputs, failed modeled accesses, and
invalid nested gallop calls return `none`.  The allocation guard and bounded
loop exhaustion remain observable and distinct in `MergeLoResult`.

The ordinary and galloping loops are represented by an explicit phase
machine.  Every recursive step consumes at least one live run entry, so the
input-size fuel is exposed only through the result flag and not as a caller
parameter.  Equality selects A while merging forward.  Galloping preserves
the C branch where an inconsistent but total comparator can consume all of A.

Version one has a pure Boolean comparator, so CPython's comparator-error jumps
to `Fail` and their negative result are deliberately absent.  The physical
temp-to-data copyback shared by C's `Succeed` and `Fail` labels remains on the
successful path.  Distinct temp/data block copies model `sortslice_memcpy`;
blocks moved within `data` use overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Compare a natural run count against a signed `Py_ssize_t`, preserving the
C signed comparison even for a raw model state with an unusual threshold. -/
def mergeLoCountAtLeastWord (count : Nat) (threshold : PySSize) : Bool :=
  !((BitVec.ofNat 64 count : PySSize).slt threshold)

def mergeLoCopyAIncr? (machine : MergeLoMachine κ ν) :
    Option (MergeLoMachine κ ν) := do
  let entry ← mergeLoTempRead? machine.state.a machine.aPos
  let data ← machine.state.data.write? machine.dest entry
  pure
    { machine with
      state := { machine.state with data := data }
      dest := machine.dest + 1
      aPos := machine.aPos + 1
      na := machine.na - 1 }

def mergeLoCopyBIncr? (machine : MergeLoMachine κ ν) :
    Option (MergeLoMachine κ ν) := do
  let entry ← machine.state.data.read? machine.bPos
  let data ← machine.state.data.write? machine.dest entry
  pure
    { machine with
      state := { machine.state with data := data }
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }

/-- The C `Succeed` label and its fallthrough into the shared remainder-copy
tail.  Comparator-error entry through C's `Fail` label is outside the total
Boolean comparator model, so this helper keeps the copyback and returns success. -/
def mergeLoSucceed? (machine : MergeLoMachine κ ν) :
    Option (MergeLoResult κ ν) := do
  let state ← mergeLoMemcpyTempToData? .finalTempToData rfl
    machine.na machine.state machine.dest machine.aPos
  pure (mergeLoSuccess state)

/-- The C `CopyB` label: shift the right remainder, then place the unique
remaining left entry at the end. -/
def mergeLoCopyB? (machine : MergeLoMachine κ ν) :
    Option (MergeLoResult κ ν) := do
  if machine.na = 1 ∧ 0 < machine.nb then
    let data ← mergeDataMemmove? .loCopyBTail machine.state.data
      machine.dest machine.bPos machine.nb
    let state := { machine.state with data := data }
    let entry ← mergeLoTempRead? state.a machine.aPos
    let data ← state.data.write? (machine.dest + Int.ofNat machine.nb) entry
    pure (mergeLoSuccess { state with data := data })
  else
    none

def mergeLoGallopFuelFailure
    (machine : MergeLoMachine κ ν) : Option (MergeLoResult κ ν) :=
  some (mergeLoOutOfFuel machine.state)

/-- One complete galloping-mode iteration.  Its continuation is supplied so
the structurally recursive driver remains the sole owner of outer fuel. -/
def mergeLoGallopRound?
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν)) :
    Option (MergeLoResult κ ν) := do
  if machine.na ≤ 1 ∨ machine.nb = 0 then
    none
  else
    let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else
        machine.minGallop
    let state := { machine.state with min_gallop := minGallop }
    let machine := { machine with state := state, minGallop := minGallop }
    let firstB ← machine.state.data.read? machine.bPos
    let activeA ← mergeLoTempRun? machine.state.a machine.aPos machine.na
    mergeLoBindOptionAcross
        (gallopRight? machine.state activeA 0 firstB.key machine.na 0) fun gallopA =>
      if gallopA.fuelExhausted then
        mergeLoGallopFuelFailure machine
      else
        let aCount := gallopA.index
        if aCount > machine.na then
          none
        else do
          let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl
            aCount machine.state machine.dest machine.aPos
          let machine : MergeLoMachine κ ν :=
            { machine with
              state := state
              dest := machine.dest + Int.ofNat aCount
              aPos := machine.aPos + aCount
              na := machine.na - aCount }
          -- Preserve C's inconsistent-comparator hedge: the gallop may consume
          -- all of A even though ordinary merge invariants expect a survivor.
          if machine.na = 0 then
            mergeLoSucceed? machine
          else if machine.na = 1 then
            mergeLoCopyB? machine
          else
            let machine ← mergeLoCopyBIncr? machine
            if machine.nb = 0 then
              mergeLoSucceed? machine
            else
              let firstA ← mergeLoTempRead? machine.state.a machine.aPos
              mergeLoBindOptionAcross
                  (gallopLeft? machine.state machine.state.data
                    machine.bPos firstA.key machine.nb 0) fun gallopB =>
                if gallopB.fuelExhausted then
                  mergeLoGallopFuelFailure machine
                else
                  let bCount := gallopB.index
                  if bCount > machine.nb then
                    none
                  else do
                    let data ← mergeDataMemmove? .loGallopB machine.state.data
                      machine.dest machine.bPos bCount
                    let machine : MergeLoMachine κ ν :=
                      { machine with
                        state := { machine.state with data := data }
                        dest := machine.dest + Int.ofNat bCount
                        bPos := machine.bPos + Int.ofNat bCount
                        nb := machine.nb - bCount }
                    if machine.nb = 0 then
                      mergeLoSucceed? machine
                    else
                      let machine ← mergeLoCopyAIncr? machine
                      if machine.na = 1 then
                        mergeLoCopyB? machine
                      else
                        next machine aCount bCount

def mergeLoLoop? :
    Nat → MergeLoMachine κ ν → MergeLoPhase → Option (MergeLoResult κ ν)
  | 0, machine, _ => some (mergeLoOutOfFuel machine.state)
  | fuel + 1, machine, .ordinary aCount bCount => do
      if machine.na ≤ 1 ∨ machine.nb = 0 then
        none
      else
        let firstA ← mergeLoTempRead? machine.state.a machine.aPos
        let firstB ← machine.state.data.read? machine.bPos
        if iflt machine.state.key_compare firstB.key firstA.key then
          let machine ← mergeLoCopyBIncr? machine
          let bCount := bCount + 1
          if machine.nb = 0 then
            mergeLoSucceed? machine
          else if mergeLoCountAtLeastWord bCount machine.minGallop then
            mergeLoLoop? fuel
              { machine with minGallop := machine.minGallop + 1 }
              .galloping
          else
            mergeLoLoop? fuel machine (.ordinary 0 bCount)
        else
          let machine ← mergeLoCopyAIncr? machine
          let aCount := aCount + 1
          if machine.na = 1 then
            mergeLoCopyB? machine
          else if mergeLoCountAtLeastWord aCount machine.minGallop then
            mergeLoLoop? fuel
              { machine with minGallop := machine.minGallop + 1 }
              .galloping
          else
            mergeLoLoop? fuel machine (.ordinary aCount 0)
  | fuel + 1, machine, .galloping =>
      mergeLoGallopRound? machine fun machine aCount bCount =>
        if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
          mergeLoLoop? fuel machine .galloping
        else
          let minGallop := machine.minGallop + 1
          let state := { machine.state with min_gallop := minGallop }
          mergeLoLoop? fuel
            { machine with state := state, minGallop := minGallop }
            (.ordinary 0 0)

/-! ## Public transcription -/

/-- Transcription of CPython's stable left-to-right merge.

`ssa` and `ssb` are signed pointer-like indices into `state.data`.  The public
guard mirrors the C assertion domain: both runs are positive and representable,
and the right run begins immediately after the left run.  The caller-side
choice `na ≤ nb` and endpoint ordering are intentionally not rechecked here,
matching their status as `merge_at` obligations in the C source.
-/
def mergeLo? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    Option (MergeLoResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 na)
    if allocated.outcome = .guardRejected then
      some (mergeLoFailure allocated.state)
    else do
      let state ← mergeLoMemcpyDataToTemp? .initialDataToTemp rfl
        na allocated.state 0 ssa
      let machine : MergeLoMachine κ ν :=
        { state := state
          dest := ssa
          aPos := 0
          bPos := ssb
          na := na
          nb := nb
          minGallop := state.min_gallop }
      let machine ← mergeLoCopyBIncr? machine
      if machine.nb = 0 then
        mergeLoSucceed? machine
      else if machine.na = 1 then
        mergeLoCopyB? machine
      else
        mergeLoLoop? (na + nb + 1) machine (.ordinary 0 0)
  else
    none

end CPythonListsort
