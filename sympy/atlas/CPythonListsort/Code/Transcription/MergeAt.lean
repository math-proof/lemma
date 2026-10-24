/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.MergeHi
import sympy.atlas.CPythonListsort.Code.Transcription.MergeLo

/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

private def bindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Observable result of `merge_at`.  Fuel exhaustion comes only from a
bounded nested gallop or merge transcription and is kept separate from the C
return code. -/
structure MergeAtResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

private def mergeAtSuccess (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeAtOutOfFuel (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def fromMergeLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

private def fromMergeHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Replace pending runs `i` and `i+1` by their combined run.  Erasing the
second run also performs CPython's explicit slide when `i` is third-last. -/
private def combinePendingAt (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  let combined := { left with len := left.len + right.len }
  let pending := (state.pending.setIfInBounds i combined).eraseIdxIfInBounds (i + 1)
  { state with pending := pending }

/-- The exact source values retained at a post-trimming merge call site.  The
original selected runs and both gallop results are intentionally retained so
assembly proofs can connect trimming monotonicity to the gallop safety
theorems rather than to the defensive checks in `prepareMergeAt?`. -/
structure MergeAtCall (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  ssa : Int
  ssb : Int
  na : Nat
  nb : Nat
  left : PendingRun
  right : PendingRun
  firstB : SortSliceEntry κ ν
  lastA : SortSliceEntry κ ν
  trimA : GallopResult
  trimB : GallopResult

/-- The observable continuation selected after `merge_at` has updated the
pending stack and completed both trimming gallops.  Keeping the two merge
continuations explicit makes the exact state and request at the subsequent
`merge_getmem` call available to assembly proofs. -/
inductive MergeAtPreparation (κ : Type u) (ν : Type v) where
  | finished (result : MergeAtResult κ ν)
  | mergeLo (call : MergeAtCall κ ν)
  | mergeHi (call : MergeAtCall κ ν)

/-- State at the end of the trimming segment (or at its early return). -/
def MergeAtPreparation.state : MergeAtPreparation κ ν → MergeState κ ν
  | .finished result => result.state
  | .mergeLo call | .mergeHi call => call.state

/-- Execute the continuation selected by `prepareMergeAt?`. -/
def finishMergeAtPreparation? :
    MergeAtPreparation κ ν → Option (MergeAtResult κ ν)
  | .finished result => some result
  | .mergeLo call =>
      match mergeLo? call.state call.ssa call.ssb call.na call.nb with
      | none => none
      | some result => some (fromMergeLo result)
  | .mergeHi call =>
      match mergeHi? call.state call.ssa call.ssb call.na call.nb with
      | none => none
      | some result => some (fromMergeHi result)

/-- The stack-update, two gallop trims, and shorter-run dispatch prefix of
`merge_at`.  A successful `.mergeLo` or `.mergeHi` result is exactly the state
and argument tuple used by the corresponding merge routine, whose first step
is the modeled `merge_getmem` call. -/
def prepareMergeAt? (state : MergeState κ ν) (i : Nat) :
    Option (MergeAtPreparation κ ν) :=
  if 2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) then
    bindOptionAcross state.pending[i]? fun left =>
      bindOptionAcross state.pending[i + 1]? fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          let na₀ := left.len.toNat
          let nb₀ := right.len.toNat
          let call := combinePendingAt state i left right
          match call.data.read? (Int.ofNat right.base) with
          | none => none
          | some firstB =>
              bindOptionAcross
                  (gallopRight? call call.data (Int.ofNat left.base)
                    firstB.key na₀ 0) fun trimA =>
                if trimA.fuelExhausted then
                  some (.finished (mergeAtOutOfFuel call))
                else if na₀ < trimA.index then
                  none
                else
                  let ssa := left.base + trimA.index
                  let na := na₀ - trimA.index
                  if na = 0 then
                    some (.finished (mergeAtSuccess call))
                  else
                    match call.data.read? (Int.ofNat (ssa + na - 1)) with
                    | none => none
                    | some lastA =>
                        bindOptionAcross
                            (gallopLeft? call call.data (Int.ofNat right.base)
                              lastA.key nb₀ (nb₀ - 1)) fun trimB =>
                          if trimB.fuelExhausted then
                            some (.finished (mergeAtOutOfFuel call))
                          else if nb₀ < trimB.index then
                            none
                          else
                            let nb := trimB.index
                            if nb = 0 then
                              some (.finished (mergeAtSuccess call))
                            else if na ≤ nb then
                              some (.mergeLo
                                { state := call
                                  ssa := Int.ofNat ssa
                                  ssb := Int.ofNat right.base
                                  na := na
                                  nb := nb
                                  left := left
                                  right := right
                                  firstB := firstB
                                  lastA := lastA
                                  trimA := trimA
                                  trimB := trimB })
                            else
                              some (.mergeHi
                                { state := call
                                  ssa := Int.ofNat ssa
                                  ssb := Int.ofNat right.base
                                  na := na
                                  nb := nb
                                  left := left
                                  right := right
                                  firstB := firstB
                                  lastA := lastA
                                  trimA := trimA
                                  trimB := trimB })
        else
          none
  else
    none

/-- Transcription of CPython's `merge_at`.

`none` denotes an input outside the source assertion domain or a failed
modeled array access.  In particular, the function accepts exactly one of the
top two legal merge positions.  Once those checks pass, the stack is updated
before trimming, as in the source. -/
def mergeAt? (state : MergeState κ ν) (i : Nat) : Option (MergeAtResult κ ν) :=
  bindOptionAcross (prepareMergeAt? state i) finishMergeAtPreparation?

/-- Facts exported from the actual `merge_at` preparation path for a
subsequent `merge_getmem` call.  In particular, the guard-relevant state frame
is proved from the transcribed control flow, while the two trimming facts are
kept separately rather than replacing them with an assumed sum bound. -/
structure MergeAtCallsiteEvidence (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : Prop where
  leftSelected : pre.pending[i]? = some call.left
  rightSelected : pre.pending[i + 1]? = some call.right
  ssa_eq :
    call.ssa = Int.ofNat (call.left.base + call.trimA.index)
  ssb_eq : call.ssb = Int.ofNat call.right.base
  listlen_eq : call.state.listlen = pre.listlen
  basekeys_eq : call.state.basekeys = pre.basekeys
  data_eq : call.state.data = pre.data
  dataSize_eq : call.state.data.entries.size = pre.data.entries.size
  storage_eq : call.state.a = pre.a
  hasValues_eq : call.state.a.hasValues = pre.a.hasValues
  alloced_eq : call.state.alloced = pre.alloced
  pending_eq :
    call.state.pending =
      (pre.pending.setIfInBounds i
        { call.left with len := call.left.len + call.right.len }).eraseIdxIfInBounds
          (i + 1)
  firstBRead :
    call.state.data.read? (Int.ofNat call.right.base) = some call.firstB
  rightGallop :
    gallopRight? call.state call.state.data (Int.ofNat call.left.base)
      call.firstB.key call.left.len.toNat 0 = some call.trimA
  leftRemainder : call.na = call.left.len.toNat - call.trimA.index
  lastARead :
    call.state.data.read?
      (Int.ofNat (call.left.base + call.trimA.index + call.na - 1)) =
        some call.lastA
  leftGallop :
    gallopLeft? call.state call.state.data (Int.ofNat call.right.base)
      call.lastA.key call.right.len.toNat (call.right.len.toNat - 1) =
        some call.trimB
  rightRemainder : call.nb = call.trimB.index
  leftPositive : 0 < call.na
  rightPositive : 0 < call.nb

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The proof follows every nested option, early-return, and dispatch branch.
set_option maxRecDepth 10000 in

private def mergeAtSlideExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := some 7 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in

private def mergeAtPreparationShape (prepared : MergeAtPreparation Nat Nat) :
    Option (Bool × Nat × Nat) :=
  match prepared with
  | .finished _ => none
  | .mergeLo call => some (true, call.na, call.nb)
  | .mergeHi call => some (false, call.na, call.nb)

private def mergeAtLoPreparationExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := none },
            { key := 4, value := none },
            { key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 3, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtHiPreparationExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none },
            { key := 7, value := none },
            { key := 2, value := none },
            { key := 6, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 4, power := some 4 },
        { base := 4, len := 2, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can reach the
`merge_lo` call site with nonempty post-trim runs. -/
example :
    (prepareMergeAt? mergeAtLoPreparationExampleState 0).bind
      mergeAtPreparationShape = some (true, 2, 2) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can also reach the
strict complementary `merge_hi` call site. -/
example :
    (prepareMergeAt? mergeAtHiPreparationExampleState 0).bind
      mergeAtPreparationShape = some (false, 3, 2) := by
  decide

end CPythonListsort
