/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Binarysort.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Structure.CPythonListsort.Code.Transcription.Binarysort.Part2
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

/-- Fuel-bounded outer insertion loop, exported for exact traced erasure and
safety proofs. -/
def binarysortLoop? :
    Nat → MergeState κ ν → SortSlice κ ν → Int → Nat → Nat →
      Option (BinarysortResult κ ν)
  | 0, _, slice, _, n, ok =>
      some { slice := slice, fuelExhausted := decide (ok < n) }
  | fuel + 1, state, slice, base, n, ok =>
      if ok < n then
        binarysortBindOptionAcross (slice.read? (base + Int.ofNat ok)) fun pivot =>
          binarysortBindOptionAcross
              (binarysortSearch? (ok + 1) state.key_compare slice base pivot 0 ok)
              fun search =>
            if search.fuelExhausted then
              some { slice := slice, fuelExhausted := true }
            else do
              let count := ok - search.position
              let slice ← slice.memmove?
                (base + Int.ofNat (search.position + 1))
                (base + Int.ofNat search.position) count
              let slice ← slice.write? (base + Int.ofNat search.position) pivot
              binarysortLoop? fuel state slice base n (ok + 1)
      else
        some { slice := slice, fuelExhausted := false }

/-- Transcription of CPython's stable binary insertion sort. -/
def binarysort? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) : Option (BinarysortResult κ ν) :=
  if 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat then
    let ok := if ok = 0 then 1 else ok
    binarysortLoop? n state slice base n ok
  else
    none

end CPythonListsort
