/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Structure.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part3
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

/-- Every source-valid physical `reverse_slice` terminates without exhausting
its distance fuel, preserves extent and values mode, and records only in-bounds
ordinary accesses.  A key phase is valid in either storage mode; a values phase
is valid only when synchronized-values storage is present. -/
theorem reverseSlicePhaseTraced_safe (phase : ReverseSlicePhase)
    (slice : SortSlice κ ν) (lo hi : Int) (valuesPresent : Bool)
    (hlo : 0 ≤ lo) (hhi : hi ≤ Int.ofNat slice.entries.size)
    (hordered : lo ≤ hi)
    (_hphase : phase = .keys ∨ valuesPresent = true)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      ReverseSlicePhaseSafetyPost phase slice lo hi valuesPresent result := by
  by_cases hnonempty : lo < hi
  · have hloopHi : hi - 1 < Int.ofNat slice.entries.size := by omega
    have hdiffNonnegative : 0 ≤ hi - lo := by omega
    have hdiffCast : Int.ofNat (hi - lo).toNat = hi - lo := by
      simpa using Int.toNat_of_nonneg hdiffNonnegative
    have hspan : hi - 1 - lo ≤ Int.ofNat (hi - lo).toNat := by
      rw [hdiffCast]
      omega
    rcases reverseSlicePhaseLoopTraced_safe (hi - lo).toNat phase slice lo
        (hi - 1) valuesPresent hlo hloopHi hspan hMode with ⟨result, hresult⟩
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simp [reverseSlicePhaseTraced?, hordered, hnonempty,
            hresult.resultEq]
        resultFuel := hresult.resultFuel
        traceFuel := by
          simpa [reverseSlicePhaseTraced?, hordered, hnonempty] using
            hresult.traceSafe.fuel
        accessesInBounds := by
          simpa [reverseSlicePhaseTraced?, hordered, hnonempty] using
            hresult.traceSafe.bounds
        tempAccessesLive := by
          simpa [reverseSlicePhaseTraced?, hordered, hnonempty] using
            hresult.traceSafe.tempLive
        noPushes := by
          simpa [reverseSlicePhaseTraced?, hordered, hnonempty] using
            hresult.traceSafe.noPushes
        exactErasure := erase_reverseSlicePhaseTraced _ _ _ _
        valuesMode := hresult.valuesMode
        sizeEq := hresult.sizeEq }
  · have heq : lo = hi := by omega
    let result := reverseSliceResult slice false
    refine ⟨result, ?_⟩
    have hpure := ReverseTraceSafe.pure result
    exact
        { resultEq := by
            simp only [reverseSlicePhaseTraced?, hordered, hnonempty,
              if_true, if_false]
            rfl
          resultFuel := rfl
          traceFuel := by
            simpa [reverseSlicePhaseTraced?, hordered, hnonempty, result] using
              hpure.fuel
          accessesInBounds := by
            simpa [reverseSlicePhaseTraced?, hordered, hnonempty, result] using
              hpure.bounds
          tempAccessesLive := by
            simpa [reverseSlicePhaseTraced?, hordered, hnonempty, result] using
              hpure.tempLive
          noPushes := by
            simpa [reverseSlicePhaseTraced?, hordered, hnonempty, result] using
              hpure.noPushes
          exactErasure := erase_reverseSlicePhaseTraced _ _ _ _
          valuesMode := hMode
          sizeEq := rfl }

end ReverseSlicePhase
end CPythonListsort
