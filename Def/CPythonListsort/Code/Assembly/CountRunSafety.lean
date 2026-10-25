/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
/-!
# `count_run` safety

The evaluator below mirrors the reviewed `count_run` transcription while
producing its trace compositionally.  The Lean instrumentation reads the
previous entry and then the next entry; its comparator orientation and control
branch match CPython's `IF_NEXT_SMALLER`, without making a claim about C operand
evaluation order.  Every operational-equivalence-block, prefix, and whole-run
reversal delegates to the traced `sortslice_reverse` evaluator proved safe in
`ReverseSliceSafety`.

As in the v1 transcription, `BoolComparator` is total.  CPython's comparator
error/failure return path is therefore outside this model; the safety theorem is
for every total Boolean comparator, including inconsistent ones.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

def ascendingScanResult (length : Nat) (fuelExhausted : Bool) :
    AscendingScanResult :=
  { length := length, fuelExhausted := fuelExhausted }

/-- Traced ascending scan.  The instrumentation chooses a predecessor-first
read order, while the comparison itself has CPython's `next < previous`
orientation. -/
def ascendingScanTraced? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat →
      TraceResult AscendingScanResult
  | 0, _, _, _, nremaining, n =>
      let result := ascendingScanResult n (decide (n < nremaining))
      if n < nremaining then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, lt, slice, base, nremaining, n =>
      if n < nremaining then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat (n - 1))).bind fun previous =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).bind fun next =>
                if iflt lt next.key previous.key then
                  TraceResult.pure (ascendingScanResult n false)
                else
                  ascendingScanTraced? fuel lt slice base nremaining (n + 1)
      else
        TraceResult.pure (ascendingScanResult n false)

/-- Traced `REVERSE_LAST_NEQ`. -/
def reverseLastEqualTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (n neq : Nat) :
    TraceResult (ReverseEqualResult κ ν) :=
  if neq = 0 then
    TraceResult.pure { slice := slice, fuelExhausted := false }
  else
    let count := neq + 1
    let start := base + Int.ofNat n - Int.ofNat count
    (sortsliceReverseTraced? valuesPresent slice start count).map fun reversed =>
      { slice := reversed.slice, fuelExhausted := reversed.fuelExhausted }

def descendingScanResult (slice : SortSlice κ ν) (length equalTail : Nat)
    (fuelExhausted : Bool) : DescendingScanResult κ ν :=
  { slice := slice
    length := length
    equalTail := equalTail
    fuelExhausted := fuelExhausted }

/-- Traced descending scan.  It probes `next < previous` first, then
`previous < next`, and delegates every completed equality block to
`reverseLastEqualTraced?`. -/
def descendingScanTraced? :
    Nat → Bool → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat → Nat →
      TraceResult (DescendingScanResult κ ν)
  | 0, _, _, slice, _, nremaining, n, neq =>
      let result := descendingScanResult slice n neq (decide (n < nremaining))
      if n < nremaining then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, valuesPresent, lt, slice, base, nremaining, n, neq =>
      if n < nremaining then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat (n - 1))).bind fun previous =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).bind fun next =>
                if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt reversed.slice
                          base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure
                    (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)
      else
        TraceResult.pure (descendingScanResult slice n neq false)

/-- Traced completion of the descending case, including final
operational-equivalence-block reversal, whole-prefix reversal, and ascending
suffix extension. -/
def finishDescendingTraced? (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (nremaining n : Nat) :
    TraceResult (CountRunResult κ ν) :=
  (descendingScanTraced? nremaining state.a.hasValues state.key_compare slice
    base nremaining n 0).bind fun descending =>
      if descending.fuelExhausted then
        TraceResult.pure
          { slice := descending.slice
            length := descending.length
            fuelExhausted := true }
      else
        (reverseLastEqualTraced? state.a.hasValues descending.slice base
          descending.length descending.equalTail).bind fun equalTailReversed =>
            if equalTailReversed.fuelExhausted then
              TraceResult.pure
                { slice := equalTailReversed.slice
                  length := descending.length
                  fuelExhausted := true }
            else
              (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice
                base descending.length).bind fun wholeReversed =>
                  if wholeReversed.fuelExhausted then
                    TraceResult.pure
                      { slice := wholeReversed.slice
                        length := descending.length
                        fuelExhausted := true }
                  else
                    (ascendingScanTraced? nremaining state.key_compare
                      wholeReversed.slice base nremaining descending.length).map
                        fun extended =>
                          { slice := wholeReversed.slice
                            length := extended.length
                            fuelExhausted := extended.fuelExhausted }

/-- Fully traced `count_run` evaluator. -/
def countRunTraced? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat) : TraceResult (CountRunResult κ ν) :=
  if 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX then
    (ascendingScanTraced? nremaining state.key_compare slice base nremaining 1).bind
      fun ascending =>
        if ascending.fuelExhausted then
          TraceResult.pure
            { slice := slice
              length := ascending.length
              fuelExhausted := true }
        else if ascending.length = nremaining then
          TraceResult.pure
            { slice := slice
              length := ascending.length
              fuelExhausted := false }
        else if 1 < ascending.length then
          (TraceResult.sortSliceKeysRead? slice base).bind fun first =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (ascending.length - 1))).bind fun last =>
                if iflt state.key_compare first.key last.key then
                  TraceResult.pure
                    { slice := slice
                      length := ascending.length
                      fuelExhausted := false }
                else
                  (sortsliceReverseTraced? state.a.hasValues slice base
                    ascending.length).bind fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          { slice := reversed.slice
                            length := ascending.length + 1
                            fuelExhausted := true }
                      else
                        finishDescendingTraced? state reversed.slice base nremaining
                          (ascending.length + 1)
        else
          finishDescendingTraced? state slice base nremaining
            (ascending.length + 1)
  else
    TraceResult.failure

end CPythonListsort
