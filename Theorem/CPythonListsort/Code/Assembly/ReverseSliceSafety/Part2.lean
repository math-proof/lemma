/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Structure.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
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

theorem reverseSlicePhaseLoopTraced_safe
    (fuel : Nat) (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
    (lo hi : Int) (valuesPresent : Bool)
    (hlo : 0 ≤ lo)
    (hhi : hi < Int.ofNat slice.entries.size)
    (hspan : hi - lo ≤ Int.ofNat fuel)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      ReversePhaseLoopSafetyPost fuel phase slice lo hi valuesPresent result := by
  induction fuel generalizing slice lo hi with
  | zero =>
      have hzero : Int.ofNat 0 = 0 := rfl
      have hstop : ¬lo < hi := by
        rw [hzero] at hspan
        omega
      let result := reverseSliceResult slice false
      refine ⟨result, ?_⟩
      exact
          { resultEq := by
              simp only [reverseSlicePhaseLoopTraced?, hstop, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [reverseSlicePhaseLoopTraced?, hstop, result] using
                (ReverseTraceSafe.pure result)
            exactErasure := erase_reverseSlicePhaseLoopTraced _ _ _ _ _
            valuesMode := hMode
            sizeEq := rfl }
  | succ fuel ih =>
      by_cases hactive : lo < hi
      · have hloIndex : SortSlice.IndexInBounds slice lo := by
          exact ⟨hlo, lt_trans hactive hhi⟩
        have hhiIndex : SortSlice.IndexInBounds slice hi := by
          exact ⟨by omega, hhi⟩
        rcases SortSlice.read_eq_some_of_indexInBounds slice lo hloIndex with
          ⟨left, hleftRaw⟩
        rcases SortSlice.read_eq_some_of_indexInBounds slice hi hhiIndex with
          ⟨right, hrightRaw⟩
        have hleft : (phase.readTraced? slice lo).result = some left := by
          change (phase.readTraced? slice lo).erase = some left
          simpa using hleftRaw
        have hright : (phase.readTraced? slice hi).result = some right := by
          change (phase.readTraced? slice hi).erase = some right
          simpa using hrightRaw
        rcases SortSlice.write_eq_some_of_indexInBounds slice lo right hloIndex with
          ⟨afterLeft, hafterLeftRaw⟩
        have hafterLeft :
            (phase.writeTraced? slice lo right).result = some afterLeft := by
          change (phase.writeTraced? slice lo right).erase = some afterLeft
          simpa using hafterLeftRaw
        have hafterLeftSize :
            afterLeft.entries.size = slice.entries.size :=
          SortSlice.write_entries_size_of_eq_some _ _ _ _ hafterLeftRaw
        have hhiAfterLeft : SortSlice.IndexInBounds afterLeft hi :=
          hhiIndex.of_size_eq hafterLeftSize
        rcases SortSlice.write_eq_some_of_indexInBounds afterLeft hi left
            hhiAfterLeft with ⟨afterRight, hafterRightRaw⟩
        have hafterRight :
            (phase.writeTraced? afterLeft hi left).result = some afterRight := by
          change (phase.writeTraced? afterLeft hi left).erase = some afterRight
          simpa using hafterRightRaw
        have hafterRightSize :
            afterRight.entries.size = afterLeft.entries.size :=
          SortSlice.write_entries_size_of_eq_some _ _ _ _ hafterRightRaw
        have hrightMatches := hMode.read_matches_of_eq_some hrightRaw
        have hleftMatches := hMode.read_matches_of_eq_some hleftRaw
        have hafterLeftMode := hMode.write_preserved_of_eq_some
          hrightMatches hafterLeftRaw
        have hafterRightMode := hafterLeftMode.write_preserved_of_eq_some
          hleftMatches hafterRightRaw
        have hnextLo : 0 ≤ lo + 1 := by omega
        have hnextHi : hi - 1 < Int.ofNat afterRight.entries.size := by
          rw [hafterRightSize, hafterLeftSize]
          omega
        have hnextSpan :
            hi - 1 - (lo + 1) ≤ Int.ofNat fuel := by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hspan ⊢
          omega
        rcases ih afterRight (lo + 1) (hi - 1)
            hnextLo hnextHi hnextSpan hafterRightMode with ⟨result, hrest⟩
        have hreadLeftSafe := reversePhaseRead_safe phase slice lo hloIndex
        have hreadRightSafe := reversePhaseRead_safe phase slice hi hhiIndex
        have hwriteLeftSafe := reversePhaseWrite_safe phase slice lo right hloIndex
        have hwriteRightSafe := reversePhaseWrite_safe phase afterLeft hi left
          hhiAfterLeft
        have htailSafe : ReverseTraceSafe
            ((phase.readTraced? slice hi).bind fun right =>
              (phase.writeTraced? slice lo right).bind fun afterLeft =>
                (phase.writeTraced? afterLeft hi left).bind fun afterRight =>
                  reverseSlicePhaseLoopTraced? fuel phase afterRight
                    (lo + 1) (hi - 1)) := by
          apply ReverseTraceSafe.bind _ _ right hright hreadRightSafe
          apply ReverseTraceSafe.bind _ _ afterLeft hafterLeft hwriteLeftSafe
          apply ReverseTraceSafe.bind _ _ afterRight hafterRight hwriteRightSafe
          exact hrest.traceSafe
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [reverseSlicePhaseLoopTraced?, hactive, if_true]
              simp [TraceResult.bind, hleft, hright, hafterLeft, hafterRight,
                hrest.resultEq]
            resultFuel := hrest.resultFuel
            traceSafe := by
              simp only [reverseSlicePhaseLoopTraced?, hactive, if_true]
              exact ReverseTraceSafe.bind _ _ left hleft hreadLeftSafe htailSafe
            exactErasure := erase_reverseSlicePhaseLoopTraced _ _ _ _ _
            valuesMode := hrest.valuesMode
            sizeEq := hrest.sizeEq.trans
              (hafterRightSize.trans hafterLeftSize) }
      · let result := reverseSliceResult slice false
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [reverseSlicePhaseLoopTraced?, hactive, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [reverseSlicePhaseLoopTraced?, hactive, result] using
                (ReverseTraceSafe.pure result)
            exactErasure := erase_reverseSlicePhaseLoopTraced _ _ _ _ _
            valuesMode := hMode
            sizeEq := rfl }

end ReverseSlicePhase
end CPythonListsort
