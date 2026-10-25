/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Gallop.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.Gallop
/-!
# Hinted galloping searches

These definitions transcribe CPython's separate `gallop_left` and
`gallop_right` routines.  Keeping the routines separate makes their deliberate
equality asymmetry, and the order of every comparator call, visible.

The searched run starts at the signed index `base`.  Invalid assertion inputs,
failed bounds checks, and failure of the doubling assertion return `none`.
Fuel exhaustion is represented separately in the successful result.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Observable result of either galloping search. -/
structure GallopResult where
  index : Nat
  fuelExhausted : Bool
  deriving DecidableEq, Repr

/-- Intermediate offsets produced by a gallop's exponential-search phase. -/
structure ExponentialResult where
  lastOffset : Nat
  offset : Nat
  fuelExhausted : Bool

end CPythonListsort
