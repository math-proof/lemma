/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean -/

import Def.CPythonListsort.Code.Policy.PendingLayout
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Data.List.Pairwise
import Theorem.CPythonListsort.Code.Policy.StackPowers
/-!
# Pending-stack power invariants

The pending array is unbounded in the Lean model.  This module records the
PowerSort policy facts from CPython: every stored boundary label is exactly the
result of the transcribed `powerloop` on the adjacent runs' current geometry,
and powers on older runs strictly increase in C array order and lie in the
concrete interval `1 .. 60`.  There is deliberately no
`MAX_MERGE_PENDING` guard in either invariant.
-/


namespace CPythonListsort

universe u v

def mislabeledOlder : PendingRun :=
  { base := 0, len := 1, power := some 2 }

def unlabeledNewest : PendingRun :=
  { base := 1, len := 1, power := none }

end CPythonListsort
