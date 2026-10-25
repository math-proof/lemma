/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Mathlib
/-!
# Shared traced gallop safety support

The C gallop routines search either the main key array or the temporary key
buffer.  Materializing temporary cells as a ghost `SortSlice` would erase the
backing identity and physical cell index from the access trace, so this module
uses a small source interface whose reads go directly to the represented
storage.

The left- and right-biased public safety theorems live in the adjacent
`GallopLeftSafety` and `GallopRightSafety` modules.  This file contains their
shared source model, traced evaluators, and proof-facing contracts.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Storage searched by a gallop.  `base` is the physical index corresponding
to logical index zero of the searched run. -/
inductive GallopKeySource (κ : Type u) (ν : Type v) where
  | main (slice : SortSlice κ ν) (base : Int)
  | temporary (storage : TempStorage κ ν) (base : Int)

end CPythonListsort
