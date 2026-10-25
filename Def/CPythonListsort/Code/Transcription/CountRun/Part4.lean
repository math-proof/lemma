/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/CountRun.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Structure.CPythonListsort.Code.Transcription.CountRun.Part3
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

/-- Finish the descending scan.  The `next < previous` comparison is always
made first.  Only when it is false is `previous < next` evaluated. -/
def descendingScan? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat → Nat →
      Option (DescendingScanResult κ ν)
  | 0, _, slice, _, nremaining, n, neq =>
      some
        { slice := slice
          length := n
          equalTail := neq
          fuelExhausted := decide (n < nremaining) }
  | fuel + 1, lt, slice, base, nremaining, n, neq =>
      if n < nremaining then do
        let previous ← slice.read? (base + Int.ofNat (n - 1))
        let next ← slice.read? (base + Int.ofNat n)
        if iflt lt next.key previous.key then
          let reversed ← reverseLastEqual? slice base n neq
          if reversed.fuelExhausted then
            some
              { slice := reversed.slice
                length := n
                equalTail := 0
                fuelExhausted := true }
          else
            descendingScan? fuel lt reversed.slice base nremaining (n + 1) 0
        else if iflt lt previous.key next.key then
          some
            { slice := slice
              length := n
              equalTail := neq
              fuelExhausted := false }
        else
          descendingScan? fuel lt slice base nremaining (n + 1) (neq + 1)
      else
        some
          { slice := slice
            length := n
            equalTail := neq
            fuelExhausted := false }

/-- Complete the descending case after entries through index `n - 1` have
already been resolved. -/
def finishDescending? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat) : Option (CountRunResult κ ν) := do
  let descending ←
    descendingScan? nremaining state.key_compare slice base nremaining n 0
  if descending.fuelExhausted then
    some
      { slice := descending.slice
        length := descending.length
        fuelExhausted := true }
  else
    let equalTailReversed ←
      reverseLastEqual? descending.slice base descending.length descending.equalTail
    if equalTailReversed.fuelExhausted then
      some
        { slice := equalTailReversed.slice
          length := descending.length
          fuelExhausted := true }
    else
      let wholeReversed ←
        sortsliceReverse? equalTailReversed.slice base descending.length
      if wholeReversed.fuelExhausted then
        some
          { slice := wholeReversed.slice
            length := descending.length
            fuelExhausted := true }
      else
        countRunBindOptionAcross
            (ascendingScan? nremaining state.key_compare wholeReversed.slice base
              nremaining descending.length)
            fun extended =>
          some
            { slice := wholeReversed.slice
              length := extended.length
              fuelExhausted := extended.fuelExhausted }

/-- Transcription of CPython's `count_run`.

`base` is the signed pointer-like index corresponding to `slo->keys`, and
`nremaining` is the asserted-positive, signed-`Py_ssize_t`-representable
remaining length. `none` represents an invalid assertion input or a failed
modeled access; `fuelExhausted` is kept distinct so the later safety theorem
can prove that the chosen bounds suffice.
-/
def countRun? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat) : Option (CountRunResult κ ν) :=
  if 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX then
    countRunBindOptionAcross
        (ascendingScan? nremaining state.key_compare slice base nremaining 1)
        fun ascending =>
      if ascending.fuelExhausted then
        some { slice := slice, length := ascending.length, fuelExhausted := true }
      else if ascending.length = nremaining then
        some { slice := slice, length := ascending.length, fuelExhausted := false }
      else if 1 < ascending.length then do
        let first ← slice.read? base
        let last ← slice.read? (base + Int.ofNat (ascending.length - 1))
        if iflt state.key_compare first.key last.key then
          some { slice := slice, length := ascending.length, fuelExhausted := false }
        else
          let reversed ← sortsliceReverse? slice base ascending.length
          if reversed.fuelExhausted then
            some
              { slice := reversed.slice
                length := ascending.length + 1
                fuelExhausted := true }
          else
            finishDescending? state reversed.slice base nremaining (ascending.length + 1)
      else
        finishDescending? state slice base nremaining (ascending.length + 1)
  else
    none

end CPythonListsort
