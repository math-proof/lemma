/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Binarysort.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.Binarysort
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

/-- Result of the fuel-bounded binary-search phase of `binarysort`. -/
structure BinarySearchResult where
  position : Nat
  fuelExhausted : Bool

end CPythonListsort
