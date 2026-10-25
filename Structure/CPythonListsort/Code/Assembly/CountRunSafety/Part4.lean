/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Theorem.CPythonListsort.Code.Assembly.CountRunSafety.Part4
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

structure DescendingScanSafetyPost
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (before : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (result : DescendingScanResult κ ν) : Prop where
  resultEq :
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq).result =
      some result
  resultFuel : result.fuelExhausted = false
  traceSafe : CountTraceSafe
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq)
  exactErasure :
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq).erase =
      descendingScan? fuel lt before base nremaining n neq
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  equalTailLt : result.equalTail < result.length
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

end CPythonListsort
