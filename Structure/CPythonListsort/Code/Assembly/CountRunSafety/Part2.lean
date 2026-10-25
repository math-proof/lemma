/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part2
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

structure AscendingScanSafetyPost
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat)
    (result : AscendingScanResult) : Prop where
  resultEq :
    (ascendingScanTraced? fuel lt slice base nremaining n).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    CountTraceSafe (ascendingScanTraced? fuel lt slice base nremaining n)
  exactErasure :
    (ascendingScanTraced? fuel lt slice base nremaining n).erase =
      ascendingScan? fuel lt slice base nremaining n
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining

end CPythonListsort
