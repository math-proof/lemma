/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Binarysort.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
/-!
# Stable binary insertion transcription

Invalid inputs from C's assertion domain and failed modeled array accesses
return `none`.  Fuel exhaustion remains distinct.  A comparator-false result
(including equality for a strict comparator) follows the right-hand branch of
the binary search; stability is therefore obtained for strict comparators.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- `Option.bind` written as the explicit source-order combinator used by the
binarysort transcription.  This is public so the traced assembly evaluator can
state and prove exact erasure without referring to a private generated name. -/
def binarysortBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

end CPythonListsort
