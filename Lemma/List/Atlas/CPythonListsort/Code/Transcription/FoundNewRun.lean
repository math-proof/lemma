import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Transcription.FoundNewRun
open CPythonListsort


namespace CPythonListsort

/--
[foundNewRunSuccess_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/FoundNewRun.lean)
-/
@[path]
lemma foundNewRunSuccess_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  foundNewRunSuccess state = { state := state, returnCode := 0, fuelExhausted := false } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunOutOfFuel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/FoundNewRun.lean)
-/
@[path]
lemma foundNewRunOutOfFuel_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  foundNewRunOutOfFuel state = { state := state, returnCode := -1, fuelExhausted := true } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunFromMergeAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/FoundNewRun.lean)
-/
@[path]
lemma foundNewRunFromMergeAt_eq
  {κ : Type u}
  {ν : Type v}
  {result : MergeAtResult κ ν} :
-- imply
  fromMergeAt result = { state := result.state returnCode := result.returnCode fuelExhausted := result.fuelExhausted } :=
-- proof
  rfl

end CPythonListsort


-- created on 2026-10-23
