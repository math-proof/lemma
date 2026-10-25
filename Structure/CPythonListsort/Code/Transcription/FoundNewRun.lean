/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/FoundNewRun.lean -/

import Theorem.CPythonListsort.Code.Transcription.MergeAt
import Def.CPythonListsort.Code.Transcription.Powerloop
/-!
# PowerSort policy step for a newly found run

`found_new_run` computes the node power separating the current top pending
run from the newly discovered run, collapses strictly larger powers, and then
stores the new power on the surviving top run.  The caller remains responsible
for pushing the new run.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of `found_new_run`. -/
structure FoundNewRunResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

end CPythonListsort
