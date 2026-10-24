/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.SortSliceSafety
import sympy.atlas.CPythonListsort.Code.Transcription.ReverseSlice

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

/-- Which physical `reverse_slice` call is being instrumented. -/
inductive ReverseSlicePhase where
  | keys
  | values
  deriving DecidableEq, Repr

namespace ReverseSlicePhase

def readTraced? (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
    (index : Int) : TraceResult (SortSliceEntry κ ν) :=
  match phase with
  | .keys => TraceResult.sortSliceKeysRead? slice index
  | .values => TraceResult.sortSliceValuesRead? slice index

def writeTraced? (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
    (index : Int) (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  match phase with
  | .keys => TraceResult.sortSliceKeysWrite? slice index entry
  | .values => TraceResult.sortSliceValuesWrite? slice index entry

private def reverseSliceResult (slice : SortSlice κ ν)
    (fuelExhausted : Bool) : ReverseSliceResult κ ν :=
  { slice := slice, fuelExhausted := fuelExhausted }

/-- One genuinely instrumented physical `reverse_slice` loop. -/
def reverseSlicePhaseLoopTraced? :
    Nat → ReverseSlicePhase → SortSlice κ ν → Int → Int →
      TraceResult (ReverseSliceResult κ ν)
  | 0, _, slice, lo, hi =>
      let result := reverseSliceResult slice (decide (lo < hi))
      if lo < hi then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, phase, slice, lo, hi =>
      if lo < hi then
        (phase.readTraced? slice lo).bind fun left =>
          (phase.readTraced? slice hi).bind fun right =>
            (phase.writeTraced? slice lo right).bind fun afterLeft =>
              (phase.writeTraced? afterLeft hi left).bind fun afterRight =>
                reverseSlicePhaseLoopTraced? fuel phase afterRight
                  (lo + 1) (hi - 1)
      else
        TraceResult.pure (reverseSliceResult slice false)

/-- Traced half-open `reverse_slice` for one physical array.

The returned `SortSlice` is the paired-snapshot semantic update for that
physical phase, not a literal intermediate C store.  In particular, callers
that instrument both key and values phases must run each phase from the same
pre-state and compose their traces; they must not feed the key-phase result to
the values phase. -/
def reverseSlicePhaseTraced? (phase : ReverseSlicePhase)
    (slice : SortSlice κ ν) (lo hi : Int) :
    TraceResult (ReverseSliceResult κ ν) :=
  if lo ≤ hi then
    if lo < hi then
      reverseSlicePhaseLoopTraced? (hi - lo).toNat phase slice lo (hi - 1)
    else
      TraceResult.pure (reverseSliceResult slice false)
  else
    TraceResult.failure

/-- Public key-array specialization of the traced `reverse_slice`. -/
def reverseSliceTraced? (slice : SortSlice κ ν) (lo hi : Int) :
    TraceResult (ReverseSliceResult κ ν) :=
  reverseSlicePhaseTraced? .keys slice lo hi

/-- Traced `sortslice_reverse`: complete key reversal first, then the complete
synchronized-values reversal from the same pre-state when values are present.
Both phases execute the paired snapshot update; the second phase's result is
the same reviewed reversal, while its events represent the second C array. -/
def sortsliceReverseTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (n : Nat) :
    TraceResult (ReverseSliceResult κ ν) :=
  let hi := base + Int.ofNat n
  (reverseSlicePhaseTraced? .keys slice base hi).bind fun keyResult =>
    if valuesPresent then
      reverseSlicePhaseTraced? .values slice base hi
    else
      TraceResult.pure keyResult

private structure ReverseTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

namespace ReverseTraceSafe

private theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : ReverseTraceSafe current)
    (hnext : ReverseTraceSafe (next value)) :
    ReverseTraceSafe (current.bind next) := by
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrent.fuel, hnext.fuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrent.noPushes, hnext.noPushes]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrent.bounds, hnext.bounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrent.tempLive, hnext.tempLive⟩

end ReverseTraceSafe

private structure ReversePhaseLoopSafetyPost
    (fuel : Nat) (phase : ReverseSlicePhase) (before : SortSlice κ ν)
    (lo hi : Int) (valuesPresent : Bool)
    (result : ReverseSliceResult κ ν) : Prop where
  resultEq :
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe : ReverseTraceSafe
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi)
  exactErasure :
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi).erase =
      reverseSliceLoop? fuel before lo hi
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

private theorem reverseSlicePhaseLoopTraced_safe
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

/-- Safety result for one physical half-open reversal. -/
structure ReverseSlicePhaseSafetyPost
    (phase : ReverseSlicePhase) (before : SortSlice κ ν) (lo hi : Int)
    (valuesPresent : Bool) (result : ReverseSliceResult κ ν) : Prop where
  resultEq :
    (reverseSlicePhaseTraced? phase before lo hi).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (reverseSlicePhaseTraced? phase before lo hi).trace.fuelExhausted = false
  accessesInBounds :
    (reverseSlicePhaseTraced? phase before lo hi).trace.allAccessesInBounds
  tempAccessesLive :
    (reverseSlicePhaseTraced? phase before lo hi).trace.tempPayloadAccessesLive
  noPushes :
    (reverseSlicePhaseTraced? phase before lo hi).trace.pushDepths = []
  exactErasure :
    (reverseSlicePhaseTraced? phase before lo hi).erase =
      reverseSlice? before lo hi
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

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

/-- Public safety certificate for the complete synchronized reversal. -/
structure ReverseSliceSafetyPost
    (before : SortSlice κ ν) (valuesPresent : Bool) (base : Int) (n : Nat)
    (result : ReverseSliceResult κ ν) : Prop where
  resultEq :
    (sortsliceReverseTraced? valuesPresent before base n).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (sortsliceReverseTraced? valuesPresent before base n).trace.fuelExhausted =
      false
  accessesInBounds :
    (sortsliceReverseTraced? valuesPresent before base n).trace.allAccessesInBounds
  tempAccessesLive :
    (sortsliceReverseTraced? valuesPresent before base n).trace.tempPayloadAccessesLive
  noPushes :
    (sortsliceReverseTraced? valuesPresent before base n).trace.pushDepths = []
  exactErasure :
    (sortsliceReverseTraced? valuesPresent before base n).erase =
      sortsliceReverse? before base n
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

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

/-! ## Branch and failure anti-vacuity regressions -/

private def reverseRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 12 },
        { key := 3, value := some 13 }] }

private def reverseNoValuesRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := none },
        { key := 1, value := none },
        { key := 2, value := none },
        { key := 3, value := none }] }
