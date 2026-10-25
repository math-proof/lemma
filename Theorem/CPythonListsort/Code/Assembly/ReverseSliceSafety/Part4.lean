/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Structure.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part4
/-!
# Slice-reversal safety

This module instruments the two physical phases of CPython's
`sortslice_reverse`.  A key phase is always executed; a synchronized-values
phase is executed from the same pre-state exactly when the explicit values
mode is enabled.  Each phase performs the reviewed reversal itself through
typed access wrappers, so the trace is produced by execution rather than
attached to an independently computed result.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseSlicePhase

/-- `sortslice_reverse` is adequate and safe on every valid half-open range.
The optional second physical phase is controlled by the explicit C-pointer
mode, never inferred from an individual entry.

The `n = 0` case is an intentional totalization of the Lean model: CPython's
body decrements its exclusive high pointer before testing it, while every
reviewed C call site supplies a positive length.  Consequently the empty-range
case proved here is a model-domain extension, not a claim about executing the C
body on a zero-length range. -/
theorem sortsliceReverse_safe (valuesPresent : Bool) (slice : SortSlice κ ν)
    (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result, ReverseSliceSafetyPost slice valuesPresent base n result := by
  let hi := base + Int.ofNat n
  have hlo : 0 ≤ base := hrange.1
  have hhi : hi ≤ Int.ofNat slice.entries.size := hrange.2
  have hordered : base ≤ hi := by
    dsimp [hi]
    exact le_add_of_nonneg_right (Int.natCast_nonneg n)
  rcases reverseSlicePhaseTraced_safe .keys slice base hi valuesPresent hlo hhi
      hordered (Or.inl rfl) hMode with ⟨keyResult, hkeys⟩
  cases valuesPresent with
  | false =>
      have hkeyEq :
          (reverseSlicePhaseTraced? .keys slice base
            (base + Int.ofNat n)).result = some keyResult := by
        simpa [hi] using hkeys.resultEq
      have hkeySafe : ReverseTraceSafe
          (reverseSlicePhaseTraced? .keys slice base
            (base + Int.ofNat n)) :=
        ⟨by simpa [hi] using hkeys.traceFuel,
          by simpa [hi] using hkeys.noPushes,
          by simpa [hi] using hkeys.accessesInBounds,
          by simpa [hi] using hkeys.tempAccessesLive⟩
      have hfullSafe : ReverseTraceSafe
          (sortsliceReverseTraced? false slice base n) := by
        simpa [sortsliceReverseTraced?] using
          (ReverseTraceSafe.bind
            (reverseSlicePhaseTraced? .keys slice base (base + Int.ofNat n))
            (fun result => TraceResult.pure result) keyResult hkeyEq hkeySafe
            (ReverseTraceSafe.pure keyResult))
      refine ⟨keyResult, ?_⟩
      exact
        { resultEq := by
            simp only [sortsliceReverseTraced?]
            unfold TraceResult.bind
            rw [hkeyEq]
            rfl
          resultFuel := hkeys.resultFuel
          traceFuel := hfullSafe.fuel
          accessesInBounds := hfullSafe.bounds
          tempAccessesLive := hfullSafe.tempLive
          noPushes := hfullSafe.noPushes
          exactErasure := erase_sortsliceReverseTraced _ _ _ _
          valuesMode := hkeys.valuesMode
          sizeEq := hkeys.sizeEq }
  | true =>
      rcases reverseSlicePhaseTraced_safe .values slice base hi true hlo hhi
          hordered (Or.inr rfl) hMode with ⟨valuesResult, hvaluesPost⟩
      have hkeyEq :
          (reverseSlicePhaseTraced? .keys slice base
            (base + Int.ofNat n)).result = some keyResult := by
        simpa [hi] using hkeys.resultEq
      have hvaluesEq :
          (reverseSlicePhaseTraced? .values slice base
            (base + Int.ofNat n)).result = some valuesResult := by
        simpa [hi] using hvaluesPost.resultEq
      have hkeySafe : ReverseTraceSafe
          (reverseSlicePhaseTraced? .keys slice base
            (base + Int.ofNat n)) :=
        ⟨by simpa [hi] using hkeys.traceFuel,
          by simpa [hi] using hkeys.noPushes,
          by simpa [hi] using hkeys.accessesInBounds,
          by simpa [hi] using hkeys.tempAccessesLive⟩
      have hvaluesSafe : ReverseTraceSafe
          (reverseSlicePhaseTraced? .values slice base
            (base + Int.ofNat n)) :=
        ⟨by simpa [hi] using hvaluesPost.traceFuel,
          by simpa [hi] using hvaluesPost.noPushes,
          by simpa [hi] using hvaluesPost.accessesInBounds,
          by simpa [hi] using hvaluesPost.tempAccessesLive⟩
      have hfullSafe : ReverseTraceSafe
          (sortsliceReverseTraced? true slice base n) := by
        simpa [sortsliceReverseTraced?] using
          (ReverseTraceSafe.bind
            (reverseSlicePhaseTraced? .keys slice base (base + Int.ofNat n))
            (fun _ => reverseSlicePhaseTraced? .values slice base
              (base + Int.ofNat n)) keyResult hkeyEq hkeySafe hvaluesSafe)
      refine ⟨valuesResult, ?_⟩
      exact
        { resultEq := by
            simp only [sortsliceReverseTraced?]
            unfold TraceResult.bind
            rw [hkeyEq]
            exact hvaluesEq
          resultFuel := hvaluesPost.resultFuel
          traceFuel := hfullSafe.fuel
          accessesInBounds := hfullSafe.bounds
          tempAccessesLive := hfullSafe.tempLive
          noPushes := hfullSafe.noPushes
          exactErasure := erase_sortsliceReverseTraced _ _ _ _
          valuesMode := hvaluesPost.valuesMode
          sizeEq := hvaluesPost.sizeEq }

end ReverseSlicePhase
end CPythonListsort
