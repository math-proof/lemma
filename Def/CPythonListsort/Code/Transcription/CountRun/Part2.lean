/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/CountRun.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Structure.CPythonListsort.Code.Transcription.CountRun
/-!
# Natural-run detection transcription

This is a direct, bounded transcription of CPython's `count_run`.  The
pointer `slo` is represented by a shared `SortSlice` together with a signed
base index.  Failed accesses are returned as `none`; exhaustion of one of the
bounded loops is recorded separately in the result.

The comparison branches deliberately retain CPython's argument order.  In
particular, the descending scan first asks whether the next key is smaller
and only asks the reverse comparison when that answer is false.  Blocks whose
adjacent pairs are operationally equivalent (both comparison directions
return false) are reversed as they are encountered before the complete
descending run is reversed.  Interpreting those blocks as key equality, and
therefore as a stability statement, requires the later strict-weak-order node.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Scan while each next key is not strictly smaller than its predecessor.
This is used both for CPython's initial ascending attempt and for the final
extension after a descending prefix has been reversed. -/
def ascendingScan? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat →
      Option AscendingScanResult
  | 0, _, _, _, nremaining, n =>
      some { length := n, fuelExhausted := decide (n < nremaining) }
  | fuel + 1, lt, slice, base, nremaining, n =>
      if n < nremaining then
        countRunBindOptionAcross (slice.read? (base + Int.ofNat (n - 1))) fun previous =>
          countRunBindOptionAcross (slice.read? (base + Int.ofNat n)) fun next =>
            if iflt lt next.key previous.key then
              some { length := n, fuelExhausted := false }
            else
              ascendingScan? fuel lt slice base nremaining (n + 1)
      else
        some { length := n, fuelExhausted := false }

end CPythonListsort
