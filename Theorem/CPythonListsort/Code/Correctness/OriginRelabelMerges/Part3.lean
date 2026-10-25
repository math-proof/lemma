/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.OriginRelabelMerges.Part2
/-!
# Origin-relabel equivariance for merge evaluators

The reverse-mode transport changes only the recorded origins carried by
occurrence keys.  This module proves that temporary-storage allocation,
galloping, and both concrete merge engines commute with that relabeling.
These are evaluator equations only: no ordering or stability law is assumed.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem mirrorMergeLoResult_state (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeLoResult_returnCode (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorMergeLoResult_fuelExhausted (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).fuelExhausted = result.fuelExhausted := rfl

@[simp] theorem mirrorMergeLoMachine_state (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).state =
      mirrorMergeState size machine.state := rfl

@[simp] theorem mirrorMergeLoMachine_dest (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).dest = machine.dest := rfl

@[simp] theorem mirrorMergeLoMachine_aPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).aPos = machine.aPos := rfl

@[simp] theorem mirrorMergeLoMachine_bPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).bPos = machine.bPos := rfl

@[simp] theorem mirrorMergeLoMachine_na (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).na = machine.na := rfl

@[simp] theorem mirrorMergeLoMachine_nb (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).nb = machine.nb := rfl

@[simp] theorem mirrorMergeLoMachine_minGallop (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).minGallop = machine.minGallop := rfl

end CPythonListsort
