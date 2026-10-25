/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Binarysort.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.Binarysort.Part2
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

structure BinarysortResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  fuelExhausted : Bool
  deriving DecidableEq, Repr

end CPythonListsort
