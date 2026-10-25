/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Mathlib
import Inductive.CPythonListsort.Code.Assembly.GallopSafety
/-!
# Shared traced gallop safety support

The C gallop routines search either the main key array or the temporary key
buffer.  Materializing temporary cells as a ghost `SortSlice` would erase the
backing identity and physical cell index from the access trace, so this module
uses a small source interface whose reads go directly to the represented
storage.

The left- and right-biased public safety theorems live in the adjacent
`GallopLeftSafety` and `GallopRightSafety` modules.  This file contains their
shared source model, traced evaluators, and proof-facing contracts.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace GallopKeySource

/-- Physical index corresponding to logical index zero. -/
def base : GallopKeySource κ ν → Int
  | .main _ base => base
  | .temporary _ base => base

/-- Number of physical logical cells in the represented storage. -/
def extent : GallopKeySource κ ν → Nat
  | .main slice _ => slice.entries.size
  | .temporary storage _ => storage.cells.size

/-- Untraced direct read at a logical index relative to `base`. -/
def read? (source : GallopKeySource κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  let physical := source.base + index
  match source with
  | .main slice _ => slice.read? physical
  | .temporary storage _ =>
      if 0 ≤ physical then storage.cells[physical.toNat]?.bind id else none

/-- Traced direct read.  Temporary reads retain the actual backing and the
physical logical-cell index; no temporary slice is materialized. -/
def readTraced? (source : GallopKeySource κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  let physical := source.base + index
  match source with
  | .main slice _ => TraceResult.sortSliceKeysRead? slice physical
  | .temporary storage _ => TraceResult.tempPayloadRead? storage physical

/-- A searched prefix is physically in bounds and every cell in it is
initialized.  Initialization is automatic for main data and an explicit,
honest premise for temporary storage. -/
def ValidRange (source : GallopKeySource κ ν) (n : Nat) : Prop :=
  0 ≤ source.base ∧
    source.base + Int.ofNat n ≤ Int.ofNat source.extent ∧
    ∀ i < n, ∃ entry, source.read? (Int.ofNat i) = some entry

/-- Temporary backing is live; main data satisfies this vacuously. -/
def Live : GallopKeySource κ ν → Prop
  | .main _ _ => True
  | .temporary storage _ => storage.Live

/-- A direct source presents exactly the same logical keys as a reviewed
`SortSlice` call throughout the searched half-open range `[0, n)`.  The two
bases are intentionally independent: a temporary source can retain its real
physical offset while the materialized transcription slice starts at zero. -/
def AgreesWithSlice (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (n : Nat) : Prop :=
  ∀ index : Int, 0 ≤ index → index < Int.ofNat n →
    source.read? index = slice.read? (sliceBase + index)

/-! ## Generic untraced evaluators -/

/-- Exponential search to the right for the left-biased gallop. -/
def gallopLeftRightExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat (hint + offset))) fun entry =>
          if iflt lt entry.key key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftRightExponentialFromSource? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else none
          else some {
            lastOffset := lastOffset
            offset := offset
            fuelExhausted := false }
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Exponential search to the left for the left-biased gallop. -/
def gallopLeftLeftExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt entry.key key then
            some {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopLeftLeftExponentialFromSource? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else none
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Binary finishing phase for the left-biased gallop. -/
def gallopLeftBinaryFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, lower, upper =>
      some {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (source.read? (Int.ofNat middle)) fun entry =>
          if iflt lt entry.key key then
            gallopLeftBinaryFromSource? fuel lt source key (middle + 1) upper
          else gallopLeftBinaryFromSource? fuel lt source key lower middle
      else some {
        index := upper
        fuelExhausted := false }

/-- Exponential search to the left for the right-biased gallop. -/
def gallopRightLeftExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt key entry.key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopRightLeftExponentialFromSource? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else none
          else some {
            lastOffset := lastOffset
            offset := offset
            fuelExhausted := false }
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Exponential search to the right for the right-biased gallop. -/
def gallopRightRightExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat (hint + offset))) fun entry =>
          if iflt lt key entry.key then
            some {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopRightRightExponentialFromSource? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else none
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Binary finishing phase for the right-biased gallop. -/
def gallopRightBinaryFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, lower, upper =>
      some {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (source.read? (Int.ofNat middle)) fun entry =>
          if iflt lt key entry.key then
            gallopRightBinaryFromSource? fuel lt source key lower middle
          else gallopRightBinaryFromSource? fuel lt source key (middle + 1) upper
      else some {
        index := upper
        fuelExhausted := false }

/-- Finish the left-biased search after its exponential phase. -/
def finishGallopLeftFromSource? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some {
          index := lower
          fuelExhausted := true }
      else gallopLeftBinaryFromSource? fuel lt source key lower upper
    else none
  else none

/-- Finish the right-biased search after its exponential phase. -/
def finishGallopRightFromSource? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some {
          index := lower
          fuelExhausted := true }
      else gallopRightBinaryFromSource? fuel lt source key lower upper
    else none
  else none

/-- Left-biased gallop over a direct key source. -/
def gallopLeftFromSource? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (source.read? (Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare hinted.key key then do
        let maxOffset := n - hint
        let exponential ← gallopLeftRightExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
      else do
        let maxOffset := hint + 1
        let exponential ← gallopLeftLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
  else none

/-- Right-biased gallop over a direct key source. -/
def gallopRightFromSource? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (source.read? (Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare key hinted.key then do
        let maxOffset := hint + 1
        let exponential ← gallopRightLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
      else do
        let maxOffset := n - hint
        let exponential ← gallopRightRightExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
  else none

/-! ## Traced evaluators -/

def tracedExponentialResult (result : ExponentialResult) :
    TraceResult ExponentialResult :=
  if result.fuelExhausted then
    (TraceResult.pure result).markFuelExhausted
  else TraceResult.pure result

def tracedGallopResult (result : GallopResult) : TraceResult GallopResult :=
  if result.fuelExhausted then
    (TraceResult.pure result).markFuelExhausted
  else TraceResult.pure result

def gallopLeftRightExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat (hint + offset))).bind fun entry =>
          if iflt lt entry.key key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftRightExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure
          else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopLeftLeftExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat hint - Int.ofNat offset)).bind fun entry =>
          if iflt lt entry.key key then
            TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopLeftLeftExponentialTraced? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else TraceResult.failure
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopLeftBinaryTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      TraceResult GallopResult
  | 0, _, _, _, lower, upper =>
      tracedGallopResult {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        (source.readTraced? (Int.ofNat middle)).bind fun entry =>
          if iflt lt entry.key key then
            gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
          else gallopLeftBinaryTraced? fuel lt source key lower middle
      else TraceResult.pure {
        index := upper
        fuelExhausted := false }

def gallopRightLeftExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat hint - Int.ofNat offset)).bind fun entry =>
          if iflt lt key entry.key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopRightLeftExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure
          else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopRightRightExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat (hint + offset))).bind fun entry =>
          if iflt lt key entry.key then
            TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopRightRightExponentialTraced? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else TraceResult.failure
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopRightBinaryTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      TraceResult GallopResult
  | 0, _, _, _, lower, upper =>
      tracedGallopResult {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        (source.readTraced? (Int.ofNat middle)).bind fun entry =>
          if iflt lt key entry.key then
            gallopRightBinaryTraced? fuel lt source key lower middle
          else gallopRightBinaryTraced? fuel lt source key (middle + 1) upper
      else TraceResult.pure {
        index := upper
        fuelExhausted := false }

def finishGallopLeftTraced? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    TraceResult GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        tracedGallopResult {
          index := lower
          fuelExhausted := true }
      else gallopLeftBinaryTraced? fuel lt source key lower upper
    else TraceResult.failure
  else TraceResult.failure

def finishGallopRightTraced? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    TraceResult GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        tracedGallopResult {
          index := lower
          fuelExhausted := true }
      else gallopRightBinaryTraced? fuel lt source key lower upper
    else TraceResult.failure
  else TraceResult.failure

/-- Traced left-biased gallop over either main or temporary storage. -/
def gallopLeftTraced? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    TraceResult GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    (source.readTraced? (Int.ofNat hint)).bind fun hinted =>
      if iflt state.key_compare hinted.key key then
        (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source key hint
          (n - hint) 0 1).bind fun exponential =>
            let offset := min exponential.offset (n - hint)
            finishGallopLeftTraced? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
      else
        (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source key hint
          (hint + 1) 0 1).bind fun exponential =>
            let offset := min exponential.offset (hint + 1)
            finishGallopLeftTraced? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat offset)
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
  else TraceResult.failure

/-- Traced right-biased gallop over either main or temporary storage. -/
def gallopRightTraced? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    TraceResult GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    (source.readTraced? (Int.ofNat hint)).bind fun hinted =>
      if iflt state.key_compare key hinted.key then
        (gallopRightLeftExponentialTraced? (n + 1) state.key_compare source key hint
          (hint + 1) 0 1).bind fun exponential =>
            let offset := min exponential.offset (hint + 1)
            finishGallopRightTraced? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat offset)
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
      else
        (gallopRightRightExponentialTraced? (n + 1) state.key_compare source key hint
          (n - hint) 0 1).bind fun exponential =>
            let offset := min exponential.offset (n - hint)
            finishGallopRightTraced? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
  else TraceResult.failure

/-! ## Absence of merge-memory boundary and merge-policy events

Gallops read either the main keys or the live temporary payload, but they do
not cross a `merge_init`, `merge_getmem`, directional-merge, or
`merge_freemem` boundary.  The helper inductions below cover the complete
traced evaluators, including rejected reads, arithmetic-guard failures, and
fuel-exhausted results. -/

/-- Internal proof-facing shorthand for a trace fragment that emits no
merge-memory boundary or merge-policy event. -/
def GallopMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

/-! ## Shared safety contracts -/

/-- The trace-only obligations shared by every gallop phase. -/
def GallopTraceSafe (execution : TraceResult α) : Prop :=
  execution.trace.fuelExhausted = false ∧
    execution.trace.pushDepths = [] ∧
    execution.trace.allAccessesInBounds ∧
    execution.trace.tempPayloadAccessesLive

/-! ### Auditable left/right comparator duality -/

/-- Swapping the arguments and negating the Boolean result turns the
left-biased branch test into the right-biased branch test.  No law of the
original comparator is used. -/
def gallopComparatorDual (lt : BoolComparator κ) : BoolComparator κ :=
  fun left right => !(lt right left)

/-- State obtained by replacing only the comparator with the auditable dual.
All geometry and storage fields are unchanged. -/
def gallopDualState (state : MergeState κ ν) : MergeState κ ν :=
  { state with key_compare := gallopComparatorDual state.key_compare }

end GallopKeySource
end CPythonListsort
