/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.Gallop
import sympy.atlas.CPythonListsort.Code.Transcription.MergeMemory

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

/-- Short-circuiting option composition used by the exported `merge_lo` core.
The dedicated name keeps later traced/refinement proofs independent of private
declaration names in this module. -/
def mergeLoBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Observable result of the `merge_lo` transcription.  A negative return
code with `fuelExhausted = false` is the deterministic `merge_getmem` guard
failure. -/
structure MergeLoResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

def mergeLoFailure (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := false }

def mergeLoOutOfFuel (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

def mergeLoSuccess (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

/-! ## Temporary-slice movement -/

/-- The three `sortslice_memcpy` sites in CPython's `merge_lo`, kept separate
so source coverage and backing direction remain machine-visible. -/
inductive MergeLoMemcpyCallsite where
  | initialDataToTemp
  | gallopTempToData
  | finalTempToData
  deriving DecidableEq, Repr

namespace MergeLoMemcpyCallsite

/-- Destination and source regions used by one pinned `merge_lo` memcpy site. -/
def backings : MergeLoMemcpyCallsite → MergeMemcpyBackings
  | .initialDataToTemp =>
      { destination := .temporary, source := .main }
  | .gallopTempToData | .finalTempToData =>
      { destination := .main, source := .temporary }

end MergeLoMemcpyCallsite

/-- Every memcpy-class bulk move in `merge_lo` crosses the main and temporary
regions.  The evaluator below couples every such move to one of these tags. -/
theorem mergeLo_memcpyCallsite_distinct (site : MergeLoMemcpyCallsite) :
    site.backings.Distinct := by
  cases site <;>
    simp [MergeLoMemcpyCallsite.backings, MergeMemcpyBackings.Distinct]

/-- Read one initialized logical entry from temporary merge storage. -/
def mergeLoTempRead? (storage : TempStorage κ ν) (index : Nat) :
    Option (SortSliceEntry κ ν) := do
  let cell ← storage.cells[index]?
  cell

/-- Initialize or replace one in-bounds logical temporary entry. -/
def mergeLoTempWrite? (storage : TempStorage κ ν) (index : Nat)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if h : index < storage.cells.size then
    some { storage with cells := storage.cells.set index (some entry) }
  else
    none

/-- Every cell in the indicated temporary range has been initialized.  This
is the precise precondition under which materializing that range is total. -/
def MergeLoTempRangeInitialized (storage : TempStorage κ ν)
    (source count : Nat) : Prop :=
  ∀ i, i < count →
    ∃ entry, mergeLoTempRead? storage (source + i) = some entry

/-- Copy a main-list range into the distinct temporary store.  This recursive
bulk-copy implementation itself requires a pinned call-site tag and a proof of
its physical direction, so there is no untagged memcpy-capable helper for an
evaluator call to bypass. -/
def mergeLoMemcpyDataToTemp?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main }) :
    Nat → MergeState κ ν → Nat → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← state.data.read? source
      let storage ← mergeLoTempWrite? state.a destination entry
      mergeLoMemcpyDataToTemp? site hDirection count
        { state with a := storage } (destination + 1) (source + 1)

/-- Copy a temporary range into the main list.  As above, the recursive
implementation cannot be invoked without a tag proving the exact
temporary-to-main direction. -/
def mergeLoMemcpyTempToData?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary }) :
    Nat → MergeState κ ν → Int → Nat → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← mergeLoTempRead? state.a source
      let data ← state.data.write? destination entry
      mergeLoMemcpyTempToData? site hDirection count
        { state with data := data } (destination + 1) (source + 1)

/-- Materialize an initialized active part of the temporary run as a
`SortSlice`, so the shared `gallop_right` transcription can inspect it. -/
def mergeLoGatherTempEntries? :
    Nat → TempStorage κ ν → Nat → Array (SortSliceEntry κ ν) →
      Option (Array (SortSliceEntry κ ν))
  | 0, _, _, entries => some entries
  | count + 1, storage, source, entries => do
      let entry ← mergeLoTempRead? storage source
      mergeLoGatherTempEntries? count storage (source + 1) (entries.push entry)

/-- Materialize an initialized temporary range as the slice consumed by
`gallop_right`. -/
def mergeLoTempRun? (storage : TempStorage κ ν) (source count : Nat) :
    Option (SortSlice κ ν) := do
  let entries ← mergeLoGatherTempEntries? count storage source #[]
  pure { entries := entries }

/-- Legacy name for the active temporary-run materializer. -/
abbrev tempRun? (storage : TempStorage κ ν) (source count : Nat) :
    Option (SortSlice κ ν) :=
  mergeLoTempRun? storage source count

/-! ## Merge machine -/

structure MergeLoMachine (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  dest : Int
  aPos : Nat
  bPos : Int
  na : Nat
  nb : Nat
  minGallop : PySSize

inductive MergeLoPhase where
  | ordinary (aCount bCount : Nat)
  | galloping

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

/-! ## Layout-relevant structural frame -/

/-- The fields needed to transport `PendingLayout` across `merge_lo`.
Keeping them in one projection lets the recursive control-flow proof establish
all four frame facts at once. -/
private structure MergeLoLayoutFrame where
  listlen : PySSize
  basekeys : Nat
  dataSize : Nat
  pending : Array PendingRun

private def mergeLoLayoutFrame (state : MergeState κ ν) : MergeLoLayoutFrame :=
  { listlen := state.listlen
    basekeys := state.basekeys
    dataSize := state.data.entries.size
    pending := state.pending }

/-! Public executable regressions pin the ordinary-mode argument order and
stable equality branch. -/

def mergeLoStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 2, value := some 20 },
            { key := 3, value := some 32 },
            { key := 3, value := some 33 }] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeLoGallopStabilityRegressionState : MergeState Nat Nat :=
  { mergeLoStabilityRegressionState with
    min_gallop := 1
    listlen := 6
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 5, value := some 50 },
            { key := 1, value := some 10 },
            { key := 2, value := some 20 },
            { key := 3, value := some 31 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3 }

/-! The next regression deliberately uses the non-irreflexive comparator
`(· ≥ ·)`.  Its continuation always fails, so the successful result is an
observable witness that the first gallop's `index = na` result took the
`na = 0` Succeed hedge rather than continuing the round.  A strict-`<` control
on the identical geometry returns index zero and a different final ordering. -/

def mergeLoNaZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 99, value := some 99 },
            { key := 98, value := some 98 },
            { key := 0, value := some 0 }] }
    a :=
      { cells :=
          #[(some { key := 1, value := some 10 }),
            (some { key := 2, value := some 20 })]
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left ≥ right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeLoNaZeroHedgeRegressionMachine : MergeLoMachine Nat Nat :=
  { state := mergeLoNaZeroHedgeRegressionState
    dest := 0
    aPos := 0
    bPos := 2
    na := 2
    nb := 1
    minGallop := MIN_GALLOP }

def mergeLoNaZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeLoNaZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeLoNaZeroHedgeStrictControlMachine : MergeLoMachine Nat Nat :=
  { mergeLoNaZeroHedgeRegressionMachine with
    state := mergeLoNaZeroHedgeStrictControlState }
