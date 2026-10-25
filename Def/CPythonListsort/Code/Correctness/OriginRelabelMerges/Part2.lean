/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelMerges.Part2
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

/-- Relabel the occurrence-bearing state of a forward merge machine. -/
def mirrorMergeLoMachine (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    MergeLoMachine (Occurrence alpha) nu :=
  { machine with state := mirrorMergeState size machine.state }

/-- Relabel the occurrence-bearing state of a forward merge result. -/
def mirrorMergeLoResult (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    MergeLoResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

end CPythonListsort
