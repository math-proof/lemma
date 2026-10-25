/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoRegressionKernel.lean -/

import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
/-!
# Kernel-checked executable fixture for `merge_lo`

This small module keeps the closed evaluator reduction separate from the large
semantic proof module.  The exported theorem is reused there as the public
regression, so no native-code decision procedure enters the trusted proof.
-/


namespace CPythonListsort

def mergeLoCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def mergeLoCorrectnessEntry (key payload : Nat) :
    SortSliceEntry Nat Nat :=
  { key := key, value := some payload }

/-- A nonzero-base fixture with distinct payloads at an equal-key boundary,
two framed neighbors, and four allocated temporary cells. -/
def mergeLoCorrectnessRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 7
    basekeys := 0
    data :=
      { entries :=
          #[mergeLoCorrectnessEntry 99 990,
            mergeLoCorrectnessEntry 4 40,
            mergeLoCorrectnessEntry 6 60,
            mergeLoCorrectnessEntry 2 20,
            mergeLoCorrectnessEntry 4 41,
            mergeLoCorrectnessEntry 5 50,
            mergeLoCorrectnessEntry 100 1000] }
    a :=
      { cells := Array.replicate 4 none
        backing := .inline
        hasValues := true }
    alloced := 4
    pending := #[]
    key_compare := mergeLoCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end CPythonListsort
