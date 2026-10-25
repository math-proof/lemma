/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Inductive.CPythonListsort.Code.Transcription.MergeAt
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

end CPythonListsort
