/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/FoundNewRun.lean -/

import Theorem.CPythonListsort.Code.Transcription.MergeAt
import Def.CPythonListsort.Code.Transcription.Powerloop
import Def.CPythonListsort.Code.Transcription.FoundNewRun
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

set_option linter.style.nativeDecide false in
/-- The source explicitly makes an empty pending stack a no-op; in particular
it does not inspect the otherwise-invalid prospective length zero. -/
example :
    (foundNewRun?
        { foundNewRunExampleState with pending := #[] } 0).map
          (fun result =>
            (result.returnCode, result.fuelExhausted,
              result.state.pending.toList,
              result.state.data.entries.toList)) =
      some
        (0, false, [], foundNewRunExampleState.data.entries.toList) := by
  decide

set_option linter.style.nativeDecide false in
/-- Collapse uses strict `>` rather than `≥`: equality leaves both runs in
place and initializes the current top run with the computed power. -/
example :
    (foundNewRun? foundNewRunExampleState 1).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 1, power := some 2 },
           { base := 1, len := 1, power := some 2 }]) := by
  decide

end CPythonListsort
