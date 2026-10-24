import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.GallopSafety
open CPythonListsort CPythonListsort.GallopKeySource


namespace CPythonListsort.GallopKeySource

/--
[main_agreesWithSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma main_agreesWithSlice
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat} :
-- imply
  (GallopKeySource.main slice base).AgreesWithSlice slice base n := by
-- proof
  intro index _hindexNonnegative _hindexUpper
  rfl

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[AgreesWithSlice.read_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma AgreesWithSlice.read_eq
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {n : Nat}
  {index : Int}
-- given
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hindexNonnegative : 0 ≤ index)
  (hindexUpper : index < Int.ofNat n) :
-- imply
  source.read? index = slice.read? (sliceBase + index) :=
-- proof
  hagrees index hindexNonnegative hindexUpper

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[temporary_agreesWithSlice_of_entries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma temporary_agreesWithSlice_of_entries
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {start n : Nat}
  {slice : SortSlice κ ν}
-- given
  (hentries : ∀ i < n, storage.cells[start + i]?.bind id = slice.entries[i]?) :
-- imply
  (GallopKeySource.temporary storage (Int.ofNat start)).AgreesWithSlice slice 0 n := by
-- proof
  intro index hindexNonnegative hindexUpper
  let i := index.toNat
  have hindexEq : Int.ofNat i = index := Int.toNat_of_nonneg hindexNonnegative
  have hi : i < n := (Int.toNat_lt hindexNonnegative).2 hindexUpper
  rw [← hindexEq]
  have hphysical : 0 ≤ Int.ofNat start + Int.ofNat i := by
    exact add_nonneg (Int.natCast_nonneg start) (Int.natCast_nonneg i)
  change (if 0 ≤ Int.ofNat start + Int.ofNat i then
    storage.cells[(Int.ofNat start + Int.ofNat i).toNat]?.bind id else none) =
    slice.read? (0 + Int.ofNat i)
  rw [if_pos hphysical]
  have hiNonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
  simp only [zero_add, SortSlice.read?, if_pos hiNonnegative]
  have hsum : (Int.ofNat start + Int.ofNat i).toNat = start + i := by rfl
  have hitoNat : (Int.ofNat i).toNat = i := rfl
  rw [hsum, hitoNat, hentries i hi]

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[erase_readTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_readTraced
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {index : Int} :
-- imply
  (source.readTraced? index).erase = source.read? index := by
-- proof
  cases source with
  | main slice base => rfl
  | temporary storage base =>
    simp [readTraced?, read?, GallopKeySource.base,
      TraceResult.erase_tempPayloadRead]

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[trace_readTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma trace_readTraced
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {index : Int} :
-- imply
  (source.readTraced? index).trace = AccessTrace.singletonAccess .read (match source with | .main _ _ => .inputKeys | .temporary storage _ => .tempPayload storage.backing) (source.base + index) source.extent := by
-- proof
  cases source with
  | main slice base => rfl
  | temporary storage base =>
    simp [readTraced?, GallopKeySource.base, GallopKeySource.extent]

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[read_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma read_eq_some
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {n i : Nat}
-- given
  (hvalid : source.ValidRange n)
  (hi : i < n) :
-- imply
  ∃ entry, source.read? (Int.ofNat i) = some entry :=
-- proof
  hvalid.2.2 i hi

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[readTraced_inBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma readTraced_inBounds
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {n i : Nat}
-- given
  (hvalid : source.ValidRange n)
  (hi : i < n) :
-- imply
  (source.readTraced? (Int.ofNat i)).trace.allAccessesInBounds := by
-- proof
  obtain ⟨hbase, hupper, hreadable⟩ := hvalid
  rw [trace_readTraced]
  simp only [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
    List.mem_singleton, forall_eq, AccessEvent.InBounds]
  constructor
  · have hiInt : Int.ofNat i < Int.ofNat n := Int.ofNat_lt.mpr hi
    have hiNonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
    omega
  · have hiInt : Int.ofNat i < Int.ofNat n := Int.ofNat_lt.mpr hi
    omega

end CPythonListsort.GallopKeySource

namespace CPythonListsort.GallopKeySource

/--
[readTraced_live](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma readTraced_live
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {index : Int}
-- given
  (hlive : source.Live) :
-- imply
  (source.readTraced? index).trace.tempPayloadAccessesLive := by
-- proof
  rw [trace_readTraced]
  cases source with
  | main slice base => simp [AccessTrace.tempPayloadAccessesLive,
    AccessTrace.singletonAccess, AccessEvent.TempPayloadLive]
  | temporary storage base =>
    simpa [Live, TempStorage.Live, AccessTrace.tempPayloadAccessesLive,
      AccessTrace.singletonAccess, AccessEvent.TempPayloadLive] using hlive

end CPythonListsort.GallopKeySource

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_pure (value : α) :
  GallopMemoryEventFree (TraceResult.pure value) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_failure :
  GallopMemoryEventFree (TraceResult.failure : TraceResult α) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_bind (current : TraceResult α)
  (next : α → TraceResult β) (hcurrent : GallopMemoryEventFree current)
  (hnext : ∀ value, GallopMemoryEventFree (next value)) :
  GallopMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
      (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_sourceRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_sourceRead
  (source : GallopKeySource κ ν) (index : Int) :
  GallopMemoryEventFree (source.readTraced? index) := by
  simp [GallopMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_leftRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_leftRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  GallopMemoryEventFree
    (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftRightExponentialTraced?, GallopMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact gallopMemoryEventFree_failure
        · exact gallopMemoryEventFree_pure _
    · exact gallopMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_leftLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_leftLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  GallopMemoryEventFree
    (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftLeftExponentialTraced?, GallopMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact gallopMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact gallopMemoryEventFree_failure
    · exact gallopMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_rightLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_rightLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  GallopMemoryEventFree
    (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightLeftExponentialTraced?, GallopMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact gallopMemoryEventFree_failure
        · exact gallopMemoryEventFree_pure _
    · exact gallopMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_rightRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_rightRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  GallopMemoryEventFree
    (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightRightExponentialTraced?, GallopMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightRightExponentialTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact gallopMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact gallopMemoryEventFree_failure
    · exact gallopMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_leftBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_leftBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  GallopMemoryEventFree
    (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopLeftBinaryTraced?, GallopMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftBinaryTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split <;> exact ih _ _
    · exact gallopMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_rightBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_rightBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  GallopMemoryEventFree
    (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopRightBinaryTraced?, GallopMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightBinaryTraced?]
    split
    · apply gallopMemoryEventFree_bind
      · exact gallopMemoryEventFree_sourceRead _ _
      · intro entry
        split <;> exact ih _ _
    · exact gallopMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_finishLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_finishLeft
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  GallopMemoryEventFree
    (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact gallopMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact gallopMemoryEventFree_failure
  · exact gallopMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopMemoryEventFree_finishRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopMemoryEventFree_finishRight
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  GallopMemoryEventFree
    (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact gallopMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact gallopMemoryEventFree_failure
  · exact gallopMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftTraced_topLevelEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopLeftTraced_topLevelEvents_eq_nil (state : MergeState κ ν)
  (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
  GallopMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply gallopMemoryEventFree_bind
    · exact gallopMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact gallopMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopRightTraced_topLevelEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopRightTraced_topLevelEvents_eq_nil (state : MergeState κ ν)
  (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
  GallopMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply gallopMemoryEventFree_bind
    · exact gallopMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact gallopMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopLeftTraced? state source key n hint).trace.memoryEvents = [] :=
-- proof
  (gallopLeftTraced_topLevelEvents_eq_nil state source key n hint).1

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopLeftTraced? state source key n hint).trace.policyEvents = [] :=
-- proof
  (gallopLeftTraced_topLevelEvents_eq_nil state source key n hint).2

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopRightTraced? state source key n hint).trace.memoryEvents = [] :=
-- proof
  (gallopRightTraced_topLevelEvents_eq_nil state source key n hint).1

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopRightTraced? state source key n hint).trace.policyEvents = [] :=
-- proof
  (gallopRightTraced_topLevelEvents_eq_nil state source key n hint).2

end CPythonListsort

namespace CPythonListsort

/--
[TraceResult.erase_bind_gallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma TraceResult.erase_bind_gallop
  {κ : Type u}
  {ν : Type v}
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).erase = gallopBindOptionAcross current.erase (fun value => (next value).erase) := by
-- proof
  cases current with
  | mk result trace => cases result <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[erase_tracedExponentialResult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma erase_tracedExponentialResult (result : ExponentialResult) :
  (tracedExponentialResult result).erase = some result := by
  cases h : result.fuelExhausted <;>
    simp [tracedExponentialResult, h]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[erase_tracedGallopResult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma erase_tracedGallopResult (result : GallopResult) :
  (tracedGallopResult result).erase = some result := by
  cases h : result.fuelExhausted <;>
    simp [tracedGallopResult, h]

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftRightExponentialTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftRightExponentialTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).erase = gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopLeftRightExponentialTraced?,
    gallopLeftRightExponentialFromSource?]
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialTraced?,
      gallopLeftRightExponentialFromSource?]
    split
    · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg
        (gallopBindOptionAcross
          (source.read? (Int.ofNat hint + Int.ofNat offset)))
      funext entry
      by_cases hcompare : lt entry.key key = true
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
      · simp [hcompare]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftLeftExponentialTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftLeftExponentialTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).erase = gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopLeftLeftExponentialTraced?,
    gallopLeftLeftExponentialFromSource?]
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialTraced?,
      gallopLeftLeftExponentialFromSource?]
    split
    · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg
        (gallopBindOptionAcross
          (source.read? (Int.ofNat hint - Int.ofNat offset)))
      funext entry
      by_cases hcompare : lt entry.key key = true
      · simp [hcompare]
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftBinaryTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftBinaryTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {lower upper : Nat} :
-- imply
  (gallopLeftBinaryTraced? fuel lt source key lower upper).erase = gallopLeftBinaryFromSource? fuel lt source key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => simp [gallopLeftBinaryTraced?, gallopLeftBinaryFromSource?]
  | succ fuel ih =>
    simp only [gallopLeftBinaryTraced?, gallopLeftBinaryFromSource?]
    split
    · let middle := lower + (upper - lower) / 2
      rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg (gallopBindOptionAcross (source.read? (Int.ofNat middle)))
      funext entry
      by_cases hcompare : lt entry.key key = true <;> simp [hcompare, ih]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightLeftExponentialTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightLeftExponentialTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).erase = gallopRightLeftExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopRightLeftExponentialTraced?,
    gallopRightLeftExponentialFromSource?]
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialTraced?,
      gallopRightLeftExponentialFromSource?]
    split
    · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg
        (gallopBindOptionAcross
          (source.read? (Int.ofNat hint - Int.ofNat offset)))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
      · simp [hcompare]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightRightExponentialTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightRightExponentialTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).erase = gallopRightRightExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopRightRightExponentialTraced?,
    gallopRightRightExponentialFromSource?]
  | succ fuel ih =>
    simp only [gallopRightRightExponentialTraced?,
      gallopRightRightExponentialFromSource?]
    split
    · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg
        (gallopBindOptionAcross
          (source.read? (Int.ofNat hint + Int.ofNat offset)))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · simp [hcompare]
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightBinaryTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightBinaryTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {lower upper : Nat} :
-- imply
  (gallopRightBinaryTraced? fuel lt source key lower upper).erase = gallopRightBinaryFromSource? fuel lt source key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => simp [gallopRightBinaryTraced?, gallopRightBinaryFromSource?]
  | succ fuel ih =>
    simp only [gallopRightBinaryTraced?, gallopRightBinaryFromSource?]
    split
    · let middle := lower + (upper - lower) / 2
      rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
      apply congrArg (gallopBindOptionAcross (source.read? (Int.ofNat middle)))
      funext entry
      by_cases hcompare : lt key entry.key = true <;> simp [hcompare, ih]
    · simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_finishGallopLeftTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_finishGallopLeftTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exhausted : Bool} :
-- imply
  (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset exhausted).erase = finishGallopLeftFromSource? fuel lt source key n lastOffset upperOffset exhausted := by
-- proof
  by_cases houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
      rw [if_pos houter, if_pos houter]
      rw [if_pos hinner, if_pos hinner]
      cases exhausted <;> simp
    · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
      rfl
  · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
    rw [if_neg houter, if_neg houter]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_finishGallopRightTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_finishGallopRightTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exhausted : Bool} :
-- imply
  (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset exhausted).erase = finishGallopRightFromSource? fuel lt source key n lastOffset upperOffset exhausted := by
-- proof
  by_cases houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopRightTraced? finishGallopRightFromSource?
      rw [if_pos houter, if_pos houter]
      rw [if_pos hinner, if_pos hinner]
      cases exhausted <;> simp
    · unfold finishGallopRightTraced? finishGallopRightFromSource?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
      rfl
  · unfold finishGallopRightTraced? finishGallopRightFromSource?
    rw [if_neg houter, if_neg houter]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopLeftTraced? state source key n hint).erase = gallopLeftFromSource? state source key n hint := by
-- proof
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · unfold gallopLeftTraced? gallopLeftFromSource?
    rw [if_pos hinput, if_pos hinput]
    rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
    apply congrArg
      (gallopBindOptionAcross (source.read? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : iflt state.key_compare hinted.key key = true
    · rw [if_pos hcompare, if_pos hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopLeftRightExponentialTraced]
      cases hphase : gallopLeftRightExponentialFromSource? (n + 1)
        state.key_compare source key hint (n - hint) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
    · rw [if_neg hcompare, if_neg hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopLeftLeftExponentialTraced]
      cases hphase : gallopLeftLeftExponentialFromSource? (n + 1)
        state.key_compare source key hint (hint + 1) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
  · simp [gallopLeftTraced?, gallopLeftFromSource?, hinput]

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopRightTraced? state source key n hint).erase = gallopRightFromSource? state source key n hint := by
-- proof
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · unfold gallopRightTraced? gallopRightFromSource?
    rw [if_pos hinput, if_pos hinput]
    rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
    apply congrArg
      (gallopBindOptionAcross (source.read? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : iflt state.key_compare key hinted.key = true
    · rw [if_pos hcompare, if_pos hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopRightLeftExponentialTraced]
      cases hphase : gallopRightLeftExponentialFromSource? (n + 1)
        state.key_compare source key hint (hint + 1) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
    · rw [if_neg hcompare, if_neg hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopRightRightExponentialTraced]
      cases hphase : gallopRightRightExponentialFromSource? (n + 1)
        state.key_compare source key hint (n - hint) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
  · simp [gallopRightTraced?, gallopRightFromSource?, hinput]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftRightExponentialFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopLeftRightExponentialFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  gallopLeftRightExponentialFromSource? fuel lt (.main slice base) key hint
    maxOffset lastOffset offset =
    gallopLeftRightExponential? fuel lt slice base key hint maxOffset
      lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialFromSource?,
      gallopLeftRightExponential?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
      rfl
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftLeftExponentialFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopLeftLeftExponentialFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  gallopLeftLeftExponentialFromSource? fuel lt (.main slice base) key hint
    maxOffset lastOffset offset =
    gallopLeftLeftExponential? fuel lt slice base key hint maxOffset
      lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialFromSource?,
      gallopLeftLeftExponential?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc,
      sub_eq_add_neg]
      rfl
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftBinaryFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopLeftBinaryFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (lower upper : Nat) :
  gallopLeftBinaryFromSource? fuel lt (.main slice base) key lower upper =
    gallopLeftBinary? fuel lt slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftBinaryFromSource?, gallopLeftBinary?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopRightLeftExponentialFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopRightLeftExponentialFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  gallopRightLeftExponentialFromSource? fuel lt (.main slice base) key hint
    maxOffset lastOffset offset =
    gallopRightLeftExponential? fuel lt slice base key hint maxOffset
      lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialFromSource?,
      gallopRightLeftExponential?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc,
      sub_eq_add_neg]
      rfl
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopRightRightExponentialFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopRightRightExponentialFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  gallopRightRightExponentialFromSource? fuel lt (.main slice base) key hint
    maxOffset lastOffset offset =
    gallopRightRightExponential? fuel lt slice base key hint maxOffset
      lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightRightExponentialFromSource?,
      gallopRightRightExponential?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
      rfl
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopRightBinaryFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma gallopRightBinaryFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (lower upper : Nat) :
  gallopRightBinaryFromSource? fuel lt (.main slice base) key lower upper =
    gallopRightBinary? fuel lt slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightBinaryFromSource?, gallopRightBinary?]
    split
    · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
    · rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[finishGallopLeftFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma finishGallopLeftFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int) (exhausted : Bool) :
  finishGallopLeftFromSource? fuel lt (.main slice base) key n lastOffset
    upperOffset exhausted =
    finishGallopLeft? fuel lt slice base key n lastOffset upperOffset exhausted := by
  simp [finishGallopLeftFromSource?, finishGallopLeft?,
    gallopLeftBinaryFromSource_main]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[finishGallopRightFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
private lemma finishGallopRightFromSource_main
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int) (exhausted : Bool) :
  finishGallopRightFromSource? fuel lt (.main slice base) key n lastOffset
    upperOffset exhausted =
    finishGallopRight? fuel lt slice base key n lastOffset upperOffset exhausted := by
  simp [finishGallopRightFromSource?, finishGallopRight?,
    gallopRightBinaryFromSource_main]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftFromSource_main
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  gallopLeftFromSource? state (.main slice base) key n hint = gallopLeft? state slice base key n hint := by
-- proof
  simp [gallopLeftFromSource?, gallopLeft?, GallopKeySource.read?,
    GallopKeySource.base, gallopLeftRightExponentialFromSource_main,
    gallopLeftLeftExponentialFromSource_main, finishGallopLeftFromSource_main]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightFromSource_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightFromSource_main
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  gallopRightFromSource? state (.main slice base) key n hint = gallopRight? state slice base key n hint := by
-- proof
  simp [gallopRightFromSource?, gallopRight?, GallopKeySource.read?,
    GallopKeySource.base, gallopRightLeftExponentialFromSource_main,
    gallopRightRightExponentialFromSource_main, finishGallopRightFromSource_main]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftRightExponentialFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftRightExponentialFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hwindow : hint + maxOffset ≤ n) :
-- imply
  gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset = gallopLeftRightExponential? fuel lt slice sliceBase key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialFromSource?,
      gallopLeftRightExponential?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      have hindexNonnegative : 0 ≤ Int.ofNat (hint + offset) :=
        Int.natCast_nonneg _
      have hindexUpper : Int.ofNat (hint + offset) < Int.ofNat n := by
        exact Int.ofNat_lt.mpr (by omega)
      rw [hagrees _ hindexNonnegative hindexUpper]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc]
      apply congrArg (gallopBindOptionAcross _)
      funext entry
      by_cases hcompare : lt entry.key key = true
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
      · simp [hcompare]
    · rw [if_neg hprobe, if_neg hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftLeftExponentialFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftLeftExponentialFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hhint : hint < n)
  (hwindow : maxOffset ≤ hint + 1) :
-- imply
  gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset = gallopLeftLeftExponential? fuel lt slice sliceBase key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialFromSource?,
      gallopLeftLeftExponential?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      have hoffsetHint : offset ≤ hint := by omega
      have hindexNonnegative :
        0 ≤ Int.ofNat hint - Int.ofNat offset := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hindexUpper :
        Int.ofNat hint - Int.ofNat offset < Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hagrees _ hindexNonnegative hindexUpper]
      simp only [sub_eq_add_neg, add_assoc]
      apply congrArg (gallopBindOptionAcross _)
      funext entry
      by_cases hcompare : lt entry.key key = true
      · simp [hcompare]
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
    · rw [if_neg hprobe, if_neg hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftBinaryFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftBinaryFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
  {lower upper n : Nat}
-- given
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hupper : upper ≤ n) :
-- imply
  gallopLeftBinaryFromSource? fuel lt source key lower upper = gallopLeftBinary? fuel lt slice sliceBase key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftBinaryFromSource?, gallopLeftBinary?]
    by_cases hsearch : lower < upper
    · rw [if_pos hsearch, if_pos hsearch]
      let middle := lower + (upper - lower) / 2
      have hmiddleUpper : middle < upper := by
        dsimp [middle]
        omega
      have hindexNonnegative : 0 ≤ Int.ofNat middle :=
        Int.natCast_nonneg _
      have hindexUpper : Int.ofNat middle < Int.ofNat n :=
        Int.ofNat_lt.mpr (by omega)
      rw [hagrees _ hindexNonnegative hindexUpper]
      apply congrArg
        (gallopBindOptionAcross
          (slice.read? (sliceBase + Int.ofNat middle)))
      funext entry
      by_cases hcompare : lt entry.key key = true
      · simp [hcompare, ih _ _ hupper]
      · have hmiddleBound : middle ≤ n := by omega
        simp only [iflt_eq, hcompare]
        exact ih lower middle hmiddleBound
    · rw [if_neg hsearch, if_neg hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightLeftExponentialFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightLeftExponentialFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hhint : hint < n)
  (hwindow : maxOffset ≤ hint + 1) :
-- imply
  gallopRightLeftExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset = gallopRightLeftExponential? fuel lt slice sliceBase key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialFromSource?,
      gallopRightLeftExponential?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      have hoffsetHint : offset ≤ hint := by omega
      have hindexNonnegative :
        0 ≤ Int.ofNat hint - Int.ofNat offset := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hindexUpper :
        Int.ofNat hint - Int.ofNat offset < Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hagrees _ hindexNonnegative hindexUpper]
      simp only [sub_eq_add_neg, add_assoc]
      apply congrArg (gallopBindOptionAcross _)
      funext entry
      by_cases hcompare : lt key entry.key = true
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
      · simp [hcompare]
    · rw [if_neg hprobe, if_neg hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightRightExponentialFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightRightExponentialFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hwindow : hint + maxOffset ≤ n) :
-- imply
  gallopRightRightExponentialFromSource? fuel lt source key hint maxOffset lastOffset offset = gallopRightRightExponential? fuel lt slice sliceBase key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightRightExponentialFromSource?,
      gallopRightRightExponential?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      have hindexNonnegative : 0 ≤ Int.ofNat (hint + offset) :=
        Int.natCast_nonneg _
      have hindexUpper : Int.ofNat (hint + offset) < Int.ofNat n := by
        exact Int.ofNat_lt.mpr (by omega)
      rw [hagrees _ hindexNonnegative hindexUpper]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc]
      apply congrArg (gallopBindOptionAcross _)
      funext entry
      by_cases hcompare : lt key entry.key = true
      · simp [hcompare]
      · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
        simp [hcompare, hguard, ih]
    · rw [if_neg hprobe, if_neg hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightBinaryFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightBinaryFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
  {lower upper n : Nat}
-- given
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hupper : upper ≤ n) :
-- imply
  gallopRightBinaryFromSource? fuel lt source key lower upper = gallopRightBinary? fuel lt slice sliceBase key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightBinaryFromSource?, gallopRightBinary?]
    by_cases hsearch : lower < upper
    · rw [if_pos hsearch, if_pos hsearch]
      let middle := lower + (upper - lower) / 2
      have hmiddleUpper : middle < upper := by
        dsimp [middle]
        omega
      have hindexNonnegative : 0 ≤ Int.ofNat middle :=
        Int.natCast_nonneg _
      have hindexUpper : Int.ofNat middle < Int.ofNat n :=
        Int.ofNat_lt.mpr (by omega)
      rw [hagrees _ hindexNonnegative hindexUpper]
      apply congrArg
        (gallopBindOptionAcross
          (slice.read? (sliceBase + Int.ofNat middle)))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · have hmiddleBound : middle ≤ n := by omega
        simp only [iflt_eq, hcompare, if_true]
        exact ih lower middle hmiddleBound
      · simp [hcompare, ih _ _ hupper]
    · rw [if_neg hsearch, if_neg hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[finishGallopLeftFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma finishGallopLeftFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exhausted : Bool}
-- given
  (hagrees : source.AgreesWithSlice slice sliceBase n) :
-- imply
  finishGallopLeftFromSource? fuel lt source key n lastOffset upperOffset exhausted = finishGallopLeft? fuel lt slice sliceBase key n lastOffset upperOffset exhausted := by
-- proof
  by_cases houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopLeftFromSource? finishGallopLeft?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_pos hinner, if_pos hinner]
      cases exhausted with
      | false =>
        exact gallopLeftBinaryFromSource_eq_slice fuel lt source slice
          sliceBase key (lastOffset + 1).toNat upperOffset.toNat n hagrees
          (Int.toNat_le.mpr houter.2.2)
      | true => rfl
    · unfold finishGallopLeftFromSource? finishGallopLeft?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
  · unfold finishGallopLeftFromSource? finishGallopLeft?
    rw [if_neg houter, if_neg houter]

end CPythonListsort

namespace CPythonListsort

/--
[finishGallopRightFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma finishGallopRightFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exhausted : Bool}
-- given
  (hagrees : source.AgreesWithSlice slice sliceBase n) :
-- imply
  finishGallopRightFromSource? fuel lt source key n lastOffset upperOffset exhausted = finishGallopRight? fuel lt slice sliceBase key n lastOffset upperOffset exhausted := by
-- proof
  by_cases houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopRightFromSource? finishGallopRight?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_pos hinner, if_pos hinner]
      cases exhausted with
      | false =>
        exact gallopRightBinaryFromSource_eq_slice fuel lt source slice
          sliceBase key (lastOffset + 1).toNat upperOffset.toNat n hagrees
          (Int.toNat_le.mpr houter.2.2)
      | true => rfl
    · unfold finishGallopRightFromSource? finishGallopRight?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
  · unfold finishGallopRightFromSource? finishGallopRight?
    rw [if_neg houter, if_neg houter]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftFromSource_eq_slice_of_ssize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftFromSource_eq_slice_of_ssize
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnSsize : n ≤ PY_SSIZE_T_MAX) :
-- imply
  gallopLeftFromSource? state source key n hint = gallopLeft? state slice sliceBase key n hint := by
-- proof
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  unfold gallopLeftFromSource? gallopLeft?
  rw [if_pos hinput, if_pos hinput]
  have hindexNonnegative : 0 ≤ Int.ofNat hint := Int.natCast_nonneg _
  have hindexUpper : Int.ofNat hint < Int.ofNat n := Int.ofNat_lt.mpr hhint
  rw [hagrees _ hindexNonnegative hindexUpper]
  apply congrArg
    (gallopBindOptionAcross
      (slice.read? (sliceBase + Int.ofNat hint)))
  funext hinted
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · rw [if_pos hcompare, if_pos hcompare]
    dsimp only
    have hphaseEq := gallopLeftRightExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (n - hint)
      0 1 n hagrees (by omega)
    rw [hphaseEq]
    cases hphase : gallopLeftRightExponential? (n + 1) state.key_compare
      slice sliceBase key hint (n - hint) 0 1 with
    | none => rfl
    | some exponential =>
      change
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
          exponential.fuelExhausted =
          finishGallopLeft? (n + 1) state.key_compare slice sliceBase key n
            (Int.ofNat exponential.lastOffset + Int.ofNat hint)
            (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
            exponential.fuelExhausted
      exact finishGallopLeftFromSource_eq_slice (n + 1) state.key_compare
        source slice sliceBase key n
        (Int.ofNat exponential.lastOffset + Int.ofNat hint)
        (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
        exponential.fuelExhausted hagrees
  · rw [if_neg hcompare, if_neg hcompare]
    dsimp only
    have hphaseEq := gallopLeftLeftExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (hint + 1)
      0 1 n hagrees hhint (by omega)
    rw [hphaseEq]
    cases hphase : gallopLeftLeftExponential? (n + 1) state.key_compare
      slice sliceBase key hint (hint + 1) 0 1 with
    | none => rfl
    | some exponential =>
      change
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted =
          finishGallopLeft? (n + 1) state.key_compare slice sliceBase key n
            (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
            (Int.ofNat hint - Int.ofNat exponential.lastOffset)
            exponential.fuelExhausted
      exact finishGallopLeftFromSource_eq_slice (n + 1) state.key_compare
        source slice sliceBase key n
        (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
        (Int.ofNat hint - Int.ofNat exponential.lastOffset)
        exponential.fuelExhausted hagrees

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightFromSource_eq_slice_of_ssize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightFromSource_eq_slice_of_ssize
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnSsize : n ≤ PY_SSIZE_T_MAX) :
-- imply
  gallopRightFromSource? state source key n hint = gallopRight? state slice sliceBase key n hint := by
-- proof
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  unfold gallopRightFromSource? gallopRight?
  rw [if_pos hinput, if_pos hinput]
  have hindexNonnegative : 0 ≤ Int.ofNat hint := Int.natCast_nonneg _
  have hindexUpper : Int.ofNat hint < Int.ofNat n := Int.ofNat_lt.mpr hhint
  rw [hagrees _ hindexNonnegative hindexUpper]
  apply congrArg
    (gallopBindOptionAcross
      (slice.read? (sliceBase + Int.ofNat hint)))
  funext hinted
  by_cases hcompare : iflt state.key_compare key hinted.key = true
  · rw [if_pos hcompare, if_pos hcompare]
    dsimp only
    have hphaseEq := gallopRightLeftExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (hint + 1)
      0 1 n hagrees hhint (by omega)
    rw [hphaseEq]
    cases hphase : gallopRightLeftExponential? (n + 1) state.key_compare
      slice sliceBase key hint (hint + 1) 0 1 with
    | none => rfl
    | some exponential =>
      change
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted =
          finishGallopRight? (n + 1) state.key_compare slice sliceBase key n
            (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
            (Int.ofNat hint - Int.ofNat exponential.lastOffset)
            exponential.fuelExhausted
      exact finishGallopRightFromSource_eq_slice (n + 1) state.key_compare
        source slice sliceBase key n
        (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
        (Int.ofNat hint - Int.ofNat exponential.lastOffset)
        exponential.fuelExhausted hagrees
  · rw [if_neg hcompare, if_neg hcompare]
    dsimp only
    have hphaseEq := gallopRightRightExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (n - hint)
      0 1 n hagrees (by omega)
    rw [hphaseEq]
    cases hphase : gallopRightRightExponential? (n + 1) state.key_compare
      slice sliceBase key hint (n - hint) 0 1 with
    | none => rfl
    | some exponential =>
      change
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
          exponential.fuelExhausted =
          finishGallopRight? (n + 1) state.key_compare slice sliceBase key n
            (Int.ofNat exponential.lastOffset + Int.ofNat hint)
            (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
            exponential.fuelExhausted
      exact finishGallopRightFromSource_eq_slice (n + 1) state.key_compare
        source slice sliceBase key n
        (Int.ofNat exponential.lastOffset + Int.ofNat hint)
        (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
        exponential.fuelExhausted hagrees

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (_hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  gallopLeftFromSource? state source key n hint = gallopLeft? state slice sliceBase key n hint := by
-- proof
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  exact gallopLeftFromSource_eq_slice_of_ssize state source slice sliceBase key
    n hint hagrees hn hhint hnSsize

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightFromSource_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightFromSource_eq_slice
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (_hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  gallopRightFromSource? state source key n hint = gallopRight? state slice sliceBase key n hint := by
-- proof
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  exact gallopRightFromSource_eq_slice_of_ssize state source slice sliceBase key
    n hint hagrees hn hhint hnSsize

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftTraced_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftTraced_eq_slice
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  (gallopLeftTraced? state source key n hint).erase = gallopLeft? state slice sliceBase key n hint := by
-- proof
  rw [erase_gallopLeftTraced]
  exact gallopLeftFromSource_eq_slice state source slice sliceBase key n hint
    hvalid hagrees hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightTraced_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightTraced_eq_slice
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  (gallopRightTraced? state source key n hint).erase = gallopRight? state slice sliceBase key n hint := by
-- proof
  rw [erase_gallopRightTraced]
  exact gallopRightFromSource_eq_slice state source slice sliceBase key n hint
    hvalid hagrees hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopLeftTraced_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopLeftTraced_main
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopLeftTraced? state (.main slice base) key n hint).erase = gallopLeft? state slice base key n hint := by
-- proof
  rw [erase_gallopLeftTraced, gallopLeftFromSource_main]

end CPythonListsort

namespace CPythonListsort

/--
[erase_gallopRightTraced_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma erase_gallopRightTraced_main
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  (gallopRightTraced? state (.main slice base) key n hint).erase = gallopRight? state slice base key n hint := by
-- proof
  rw [erase_gallopRightTraced, gallopRightFromSource_main]

end CPythonListsort

namespace CPythonListsort

/--
[gallopTraceSafe_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopTraceSafe_pure
  {κ : Type u}
  {ν : Type v}
  {value : α} :
-- imply
  GallopTraceSafe (TraceResult.pure value) := by
-- proof
  refine ⟨rfl, rfl, AccessTrace.allAccessesInBounds_empty,
    AccessTrace.tempPayloadAccessesLive_empty⟩

end CPythonListsort

namespace CPythonListsort

/--
[gallopTraceSafe_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopTraceSafe_bind
  {κ : Type u}
  {ν : Type v}
  {current : TraceResult α}
  {next : α → TraceResult β}
  {value : α}
-- given
  (hresult : current.result = some value)
  (hcurrent : GallopTraceSafe current)
  (hnext : GallopTraceSafe (next value)) :
-- imply
  GallopTraceSafe (current.bind next) := by
-- proof
  rcases hcurrent with
    ⟨hcurrentFuel, hcurrentPushes, hcurrentBounds, hcurrentLive⟩
  obtain ⟨hnextFuel, hnextPushes, hnextBounds, hnextLive⟩ := hnext
  rw [GallopTraceSafe, TraceResult.trace_bind, hresult]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hcurrentFuel, hnextFuel]
  · simp [AccessTrace.compose, hcurrentPushes, hnextPushes]
  · exact (AccessTrace.allAccessesInBounds_compose _ _).2
    ⟨hcurrentBounds, hnextBounds⟩
  · exact (AccessTrace.tempPayloadAccessesLive_compose _ _).2
    ⟨hcurrentLive, hnextLive⟩

end CPythonListsort

namespace CPythonListsort

/--
[GallopKeySource.readTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma GallopKeySource.readTraced_safe
  {κ : Type u}
  {ν : Type v}
  {source : GallopKeySource κ ν}
  {n i : Nat}
-- given
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hi : i < n) :
-- imply
  ∃ entry, (source.readTraced? (Int.ofNat i)).result = some entry ∧ GallopTraceSafe (source.readTraced? (Int.ofNat i)) := by
-- proof
  obtain ⟨entry, hentry⟩ := source.read_eq_some hvalid hi
  refine ⟨entry, ?_, ?_⟩
  · simpa [TraceResult.erase] using
    (source.erase_readTraced (Int.ofNat i)).trans hentry
  · refine ⟨?_, ?_, source.readTraced_inBounds hvalid hi,
    source.readTraced_live (Int.ofNat i) hlive⟩
    · rw [source.trace_readTraced]
      rfl
    · rw [source.trace_readTraced]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[gallop_doubling_guard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallop_doubling_guard
  {κ : Type u}
  {ν : Type v}
  {offset maxOffset n : Nat}
-- given
  (hoffset : offset < maxOffset)
  (hmax : maxOffset ≤ n)
  (hn : n ≤ PY_LIST_MAX) :
-- imply
  offset ≤ (PY_SSIZE_T_MAX - 1) / 2 := by
-- proof
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hn ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftRightExponential_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftRightExponential_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hwindow : hint + maxOffset ≤ n)
  (hnmax : n ≤ PY_LIST_MAX)
  (hoffsetPositive : 0 < offset)
  (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset) :
-- imply
  ∃ result, (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).result = some result ∧ result.fuelExhausted = false ∧ result.lastOffset < result.offset ∧ result.lastOffset < maxOffset ∧ GallopTraceSafe (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset) := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero =>
    have hstop : ¬ offset < maxOffset := by omega
    let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
    refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
    · simp [gallopLeftRightExponentialTraced?, hstop,
      tracedExponentialResult, TraceResult.pure, outcome]
    · simp [gallopLeftRightExponentialTraced?, hstop,
      tracedExponentialResult]
  | succ fuel ih =>
    by_cases hprobe : offset < maxOffset
    · have hindex : hint + offset < n := by omega
      rcases source.readTraced_safe hvalid hlive hindex with
        ⟨entry, hreadResult, hreadSafe⟩
      by_cases hcompare : iflt lt entry.key key = true
      · have hmax : maxOffset ≤ n := by omega
        have hguard := gallop_doubling_guard hprobe hmax hnmax
        have hnewPositive : 0 < 2 * offset + 1 := by omega
        have hnewLast : offset < 2 * offset + 1 := by omega
        have hnewBudget : maxOffset ≤ fuel + (2 * offset + 1) := by omega
        rcases ih offset (2 * offset + 1) hnewPositive hnewLast hprobe
          hnewBudget with
          ⟨result, hresult, hnotExhausted, hresultOrder, hresultMax,
            htrace⟩
        refine ⟨result, ?_, hnotExhausted, hresultOrder, hresultMax, ?_⟩
        · simp only [gallopLeftRightExponentialTraced?, if_pos hprobe,
          TraceResult.bind, hreadResult, if_pos hcompare,
          if_pos hguard, hresult]
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat (hint + offset)))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                gallopLeftRightExponentialTraced? fuel lt source key hint
                  maxOffset offset (2 * offset + 1)
              else TraceResult.failure
            else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false })
          entry hreadResult hreadSafe
          (by simpa only [if_pos hcompare, if_pos hguard]
            using htrace)
          rwa [gallopLeftRightExponentialTraced?, if_pos hprobe]
      · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
        refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
        · simp only [gallopLeftRightExponentialTraced?, if_pos hprobe,
          TraceResult.bind, hreadResult, if_neg hcompare,
          TraceResult.pure, outcome]
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat (hint + offset)))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                gallopLeftRightExponentialTraced? fuel lt source key hint
                  maxOffset offset (2 * offset + 1)
              else TraceResult.failure
            else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false })
          entry hreadResult hreadSafe
          (by simpa only [if_neg hcompare] using
            (gallopTraceSafe_pure outcome))
          rwa [gallopLeftRightExponentialTraced?, if_pos hprobe]
    · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
      refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
      · simp [gallopLeftRightExponentialTraced?, hprobe,
        TraceResult.pure, outcome]
      · simp [gallopLeftRightExponentialTraced?, hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftLeftExponential_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftLeftExponential_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hhint : hint < n)
  (hwindow : maxOffset ≤ hint + 1)
  (hnmax : n ≤ PY_LIST_MAX)
  (hoffsetPositive : 0 < offset)
  (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset) :
-- imply
  ∃ result, (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).result = some result ∧ result.fuelExhausted = false ∧ result.lastOffset < result.offset ∧ result.lastOffset < maxOffset ∧ GallopTraceSafe (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset) := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero =>
    have hstop : ¬ offset < maxOffset := by omega
    let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
    refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
    · simp [gallopLeftLeftExponentialTraced?, hstop,
      tracedExponentialResult, TraceResult.pure, outcome]
    · simp [gallopLeftLeftExponentialTraced?, hstop,
      tracedExponentialResult]
  | succ fuel ih =>
    by_cases hprobe : offset < maxOffset
    · have hoffsetHint : offset ≤ hint := by omega
      have hindex : hint - offset < n := by omega
      rcases source.readTraced_safe hvalid hlive hindex with
        ⟨entry, hreadResultNat, hreadSafeNat⟩
      have hindexEq :
        Int.ofNat hint - Int.ofNat offset = Int.ofNat (hint - offset) := by
        exact (Int.ofNat_sub hoffsetHint).symm
      have hreadResult :
        (source.readTraced?
          (Int.ofNat hint - Int.ofNat offset)).result = some entry := by
        rwa [hindexEq]
      have hreadSafe : GallopTraceSafe
        (source.readTraced? (Int.ofNat hint - Int.ofNat offset)) := by
        rwa [hindexEq]
      by_cases hcompare : iflt lt entry.key key = true
      · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
        refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
        · simp only [gallopLeftLeftExponentialTraced?, if_pos hprobe,
          TraceResult.bind, hreadResult, if_pos hcompare,
          TraceResult.pure, outcome]
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat hint - Int.ofNat offset))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
            else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftLeftExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure)
          entry hreadResult hreadSafe
          (by simpa only [if_pos hcompare] using
            (gallopTraceSafe_pure outcome))
          rwa [gallopLeftLeftExponentialTraced?, if_pos hprobe]
      · have hmax : maxOffset ≤ n := by omega
        have hguard := gallop_doubling_guard hprobe hmax hnmax
        have hnewPositive : 0 < 2 * offset + 1 := by omega
        have hnewLast : offset < 2 * offset + 1 := by omega
        have hnewBudget : maxOffset ≤ fuel + (2 * offset + 1) := by omega
        rcases ih offset (2 * offset + 1) hnewPositive hnewLast hprobe
          hnewBudget with
          ⟨result, hresult, hnotExhausted, hresultOrder, hresultMax,
            htrace⟩
        refine ⟨result, ?_, hnotExhausted, hresultOrder, hresultMax, ?_⟩
        · simp only [gallopLeftLeftExponentialTraced?, if_pos hprobe,
          TraceResult.bind, hreadResult, if_neg hcompare,
          if_pos hguard, hresult]
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat hint - Int.ofNat offset))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
            else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftLeftExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure)
          entry hreadResult hreadSafe
          (by simpa only [if_neg hcompare, if_pos hguard] using htrace)
          rwa [gallopLeftLeftExponentialTraced?, if_pos hprobe]
    · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
      refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
      · simp [gallopLeftLeftExponentialTraced?, hprobe,
        TraceResult.pure, outcome]
      · simp [gallopLeftLeftExponentialTraced?, hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftBinary_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftBinary_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {lower upper n : Nat}
-- given
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hlowerUpper : lower ≤ upper)
  (hupper : upper ≤ n)
  (hbudget : upper - lower ≤ fuel) :
-- imply
  ∃ result, (gallopLeftBinaryTraced? fuel lt source key lower upper).result = some result ∧ result.fuelExhausted = false ∧ lower ≤ result.index ∧ result.index ≤ upper ∧ GallopTraceSafe (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
-- proof
  induction fuel generalizing lower upper with
  | zero =>
    have hstop : ¬ lower < upper := by omega
    let outcome : GallopResult := ⟨lower, false⟩
    refine ⟨outcome, ?_, rfl, Nat.le_refl lower, ?_, ?_⟩
    · simp [gallopLeftBinaryTraced?, hstop, tracedGallopResult,
      TraceResult.pure, outcome]
    · omega
    · simp [gallopLeftBinaryTraced?, hstop, tracedGallopResult]
  | succ fuel ih =>
    by_cases hsearch : lower < upper
    · let middle := lower + (upper - lower) / 2
      have hlowerMiddle : lower ≤ middle := by
        simp [middle]
      have hmiddleUpper : middle < upper := by
        dsimp [middle]
        omega
      have hmiddleIndex : middle < n := by omega
      rcases source.readTraced_safe hvalid hlive hmiddleIndex with
        ⟨entry, hreadResult, hreadSafe⟩
      by_cases hcompare : iflt lt entry.key key = true
      · have hnextOrder : middle + 1 ≤ upper := by omega
        have hnextBudget : upper - (middle + 1) ≤ fuel := by
          dsimp [middle]
          omega
        rcases ih (middle + 1) upper hnextOrder hupper hnextBudget with
          ⟨result, hresult, hnotExhausted, hresultLower, hresultUpper,
            htrace⟩
        have hreadResult' :
          (source.readTraced?
            (Int.ofNat (lower + (upper - lower) / 2))).result =
            some entry := by
          simpa only [middle] using hreadResult
        have hresult' :
          (gallopLeftBinaryTraced? fuel lt source key
            (lower + (upper - lower) / 2 + 1) upper).result =
            some result := by
          simpa only [middle] using hresult
        refine ⟨result, ?_, hnotExhausted, ?_, hresultUpper, ?_⟩
        · simp only [gallopLeftBinaryTraced?, if_pos hsearch,
          TraceResult.bind, hreadResult', if_pos hcompare, hresult']
        · omega
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat middle))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
            else gallopLeftBinaryTraced? fuel lt source key lower middle)
          entry hreadResult hreadSafe
          (by simpa only [if_pos hcompare] using htrace)
          rwa [gallopLeftBinaryTraced?, if_pos hsearch]
      · have hnextUpper : middle ≤ n := by omega
        have hnextBudget : middle - lower ≤ fuel := by
          dsimp [middle]
          omega
        rcases ih lower middle hlowerMiddle hnextUpper hnextBudget with
          ⟨result, hresult, hnotExhausted, hresultLower, hresultUpper,
            htrace⟩
        have hreadResult' :
          (source.readTraced?
            (Int.ofNat (lower + (upper - lower) / 2))).result =
            some entry := by
          simpa only [middle] using hreadResult
        have hresult' :
          (gallopLeftBinaryTraced? fuel lt source key lower
            (lower + (upper - lower) / 2)).result = some result := by
          simpa only [middle] using hresult
        refine ⟨result, ?_, hnotExhausted, hresultLower, ?_, ?_⟩
        · simp only [gallopLeftBinaryTraced?, if_pos hsearch,
          TraceResult.bind, hreadResult', if_neg hcompare, hresult']
        · omega
        · have hbound := gallopTraceSafe_bind
          (source.readTraced? (Int.ofNat middle))
          (fun readEntry =>
            if iflt lt readEntry.key key then
              gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
            else gallopLeftBinaryTraced? fuel lt source key lower middle)
          entry hreadResult hreadSafe
          (by simpa only [if_neg hcompare] using htrace)
          rwa [gallopLeftBinaryTraced?, if_pos hsearch]
    · have hequal : lower = upper := by omega
      let outcome : GallopResult := ⟨upper, false⟩
      refine ⟨outcome, ?_, rfl, ?_, Nat.le_refl upper, ?_⟩
      · simp [gallopLeftBinaryTraced?, hsearch, TraceResult.pure, outcome]
      · omega
      · simp [gallopLeftBinaryTraced?, hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[gallopComparatorDual_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopComparatorDual_apply
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {left right : κ} :
-- imply
  gallopComparatorDual lt left right = !(lt right left) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightRight_eq_leftRight_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightRight_eq_leftRight_dual
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopRightRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset = gallopLeftRightExponentialTraced? fuel (gallopComparatorDual lt) source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightRightExponentialTraced?,
      gallopLeftRightExponentialTraced?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      apply congrArg
        (TraceResult.bind
          (source.readTraced? (Int.ofNat (hint + offset))))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · simp [gallopComparatorDual, hcompare]
      · have hfalse : lt key entry.key = false :=
        Bool.eq_false_of_not_eq_true hcompare
        simp [gallopComparatorDual, hfalse, ih]
    · simp [hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightLeft_eq_leftLeft_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightLeft_eq_leftLeft_dual
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset = gallopLeftLeftExponentialTraced? fuel (gallopComparatorDual lt) source key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialTraced?,
      gallopLeftLeftExponentialTraced?]
    by_cases hprobe : offset < maxOffset
    · rw [if_pos hprobe, if_pos hprobe]
      apply congrArg
        (TraceResult.bind
          (source.readTraced? (Int.ofNat hint - Int.ofNat offset)))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · simp [gallopComparatorDual, hcompare, ih]
      · have hfalse : lt key entry.key = false :=
        Bool.eq_false_of_not_eq_true hcompare
        simp [gallopComparatorDual, hfalse]
    · simp [hprobe]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightBinary_eq_leftBinary_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightBinary_eq_leftBinary_dual
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {lower upper : Nat} :
-- imply
  gallopRightBinaryTraced? fuel lt source key lower upper = gallopLeftBinaryTraced? fuel (gallopComparatorDual lt) source key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightBinaryTraced?, gallopLeftBinaryTraced?]
    by_cases hsearch : lower < upper
    · rw [if_pos hsearch, if_pos hsearch]
      let middle := lower + (upper - lower) / 2
      apply congrArg
        (TraceResult.bind (source.readTraced? (Int.ofNat middle)))
      funext entry
      by_cases hcompare : lt key entry.key = true
      · simp [gallopComparatorDual, hcompare, ih]
      · have hfalse : lt key entry.key = false :=
        Bool.eq_false_of_not_eq_true hcompare
        simp [gallopComparatorDual, hfalse, ih]
    · simp [hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightRightExponential_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightRightExponential_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hwindow : hint + maxOffset ≤ n)
  (hnmax : n ≤ PY_LIST_MAX)
  (hoffsetPositive : 0 < offset)
  (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset) :
-- imply
  ∃ result, (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).result = some result ∧ result.fuelExhausted = false ∧ result.lastOffset < result.offset ∧ result.lastOffset < maxOffset ∧ GallopTraceSafe (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset lastOffset offset) := by
-- proof
  rw [gallopRightRight_eq_leftRight_dual]
  exact gallopLeftRightExponential_safe fuel (gallopComparatorDual lt) source
    key hint maxOffset lastOffset offset n hvalid hlive hwindow hnmax
    hoffsetPositive hlastOffset hlastMax hbudget

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightLeftExponential_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightLeftExponential_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hhint : hint < n)
  (hwindow : maxOffset ≤ hint + 1)
  (hnmax : n ≤ PY_LIST_MAX)
  (hoffsetPositive : 0 < offset)
  (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset) :
-- imply
  ∃ result, (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset).result = some result ∧ result.fuelExhausted = false ∧ result.lastOffset < result.offset ∧ result.lastOffset < maxOffset ∧ GallopTraceSafe (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset lastOffset offset) := by
-- proof
  rw [gallopRightLeft_eq_leftLeft_dual]
  exact gallopLeftLeftExponential_safe fuel (gallopComparatorDual lt) source
    key hint maxOffset lastOffset offset n hvalid hlive hhint hwindow hnmax
    hoffsetPositive hlastOffset hlastMax hbudget

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightBinary_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightBinary_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {lower upper n : Nat}
-- given
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hlowerUpper : lower ≤ upper)
  (hupper : upper ≤ n)
  (hbudget : upper - lower ≤ fuel) :
-- imply
  ∃ result, (gallopRightBinaryTraced? fuel lt source key lower upper).result = some result ∧ result.fuelExhausted = false ∧ lower ≤ result.index ∧ result.index ≤ upper ∧ GallopTraceSafe (gallopRightBinaryTraced? fuel lt source key lower upper) := by
-- proof
  rw [gallopRightBinary_eq_leftBinary_dual]
  exact gallopLeftBinary_safe fuel (gallopComparatorDual lt) source key lower
    upper n hvalid hlive hlowerUpper hupper hbudget

end CPythonListsort

namespace CPythonListsort

/--
[finishGallopLeft_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma finishGallopLeft_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
-- given
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hlast : -1 ≤ lastOffset)
  (horder : lastOffset < upperOffset)
  (hupper : upperOffset ≤ Int.ofNat n)
  (hlowerNonnegative : 0 ≤ lastOffset + 1)
  (hupperNonnegative : 0 ≤ upperOffset)
  (hfuel : n ≤ fuel) :
-- imply
  ∃ result, (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset false).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ GallopTraceSafe (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset false) := by
-- proof
  let lower := (lastOffset + 1).toNat
  let upper := upperOffset.toNat
  have hlowerUpper : lower ≤ upper := by
    apply Int.toNat_le_toNat
    omega
  have hupperNat : upper ≤ n := by
    exact Int.toNat_le.mpr hupper
  have hbudget : upper - lower ≤ fuel := by omega
  rcases gallopLeftBinary_safe fuel lt source key lower upper n hvalid hlive
    hlowerUpper hupperNat hbudget with
    ⟨result, hresult, hnotExhausted, _hresultLower, hresultUpper, htrace⟩
  have houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n := ⟨hlast, horder, hupper⟩
  have hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset :=
    ⟨hlowerNonnegative, hupperNonnegative⟩
  have hfinish :
    finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset false =
      gallopLeftBinaryTraced? fuel lt source key lower upper := by
    unfold finishGallopLeftTraced?
    rw [if_pos houter]
    rw [if_pos hinner]
    rfl
  rw [hfinish]
  exact ⟨result, hresult, hnotExhausted, by omega, htrace⟩

end CPythonListsort

namespace CPythonListsort

/--
[finishGallopRight_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma finishGallopRight_safe
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {key : κ}
  {n : Nat}
  {lastOffset upperOffset : Int}
-- given
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hlast : -1 ≤ lastOffset)
  (horder : lastOffset < upperOffset)
  (hupper : upperOffset ≤ Int.ofNat n)
  (hlowerNonnegative : 0 ≤ lastOffset + 1)
  (hupperNonnegative : 0 ≤ upperOffset)
  (hfuel : n ≤ fuel) :
-- imply
  ∃ result, (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset false).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ GallopTraceSafe (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset false) := by
-- proof
  let lower := (lastOffset + 1).toNat
  let upper := upperOffset.toNat
  have hlowerUpper : lower ≤ upper := by
    apply Int.toNat_le_toNat
    omega
  have hupperNat : upper ≤ n := by
    exact Int.toNat_le.mpr hupper
  have hbudget : upper - lower ≤ fuel := by omega
  rcases gallopRightBinary_safe fuel lt source key lower upper n hvalid hlive
    hlowerUpper hupperNat hbudget with
    ⟨result, hresult, hnotExhausted, _hresultLower, hresultUpper, htrace⟩
  have houter :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
      upperOffset ≤ Int.ofNat n := ⟨hlast, horder, hupper⟩
  have hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset :=
    ⟨hlowerNonnegative, hupperNonnegative⟩
  have hfinish :
    finishGallopRightTraced? fuel lt source key n lastOffset upperOffset false =
      gallopRightBinaryTraced? fuel lt source key lower upper := by
    unfold finishGallopRightTraced?
    rw [if_pos houter]
    rw [if_pos hinner]
    rfl
  rw [hfinish]
  exact ⟨result, hresult, hnotExhausted, by omega, htrace⟩

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeftFromSource_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopLeftFromSource_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, (gallopLeftTraced? state source key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ GallopTraceSafe (gallopLeftTraced? state source key n hint) := by
-- proof
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  rcases source.readTraced_safe hvalid hlive hhint with
    ⟨hinted, hhintedResult, hhintedSafe⟩
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · let maxOffset := n - hint
    have hmaxPositive : 0 < maxOffset := by
      dsimp [maxOffset]
      omega
    have hwindow : hint + maxOffset ≤ n := by
      dsimp [maxOffset]
      omega
    have hbudget : maxOffset ≤ (n + 1) + 1 := by omega
    rcases gallopLeftRightExponential_safe (n + 1) state.key_compare source
      key hint maxOffset 0 1 n hvalid hlive hwindow hnmax (by omega)
      (by omega) hmaxPositive hbudget with
      ⟨exponential, hexponentialResult, hexponentialFuel,
        hexponentialOrder, hexponentialMax, hexponentialTrace⟩
    let capped := min exponential.offset maxOffset
    have hexponentialCapped : exponential.lastOffset < capped := by
      dsimp [capped]
      omega
    have hcappedMax : capped ≤ maxOffset := by
      exact Nat.min_le_right _ _
    have hlast :
      (-1 : Int) ≤
        Int.ofNat exponential.lastOffset + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have horder :
      Int.ofNat exponential.lastOffset + Int.ofNat hint <
        Int.ofNat capped + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupper :
      Int.ofNat capped + Int.ofNat hint ≤ Int.ofNat n := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have hlowerNonnegative :
      0 ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint + 1 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupperNonnegative :
      0 ≤ Int.ofNat capped + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rcases finishGallopLeft_safe (n + 1) state.key_compare source key n
      (Int.ofNat exponential.lastOffset + Int.ofNat hint)
      (Int.ofNat capped + Int.ofNat hint) hvalid hlive hlast horder hupper
      hlowerNonnegative hupperNonnegative (by omega) with
      ⟨result, hfinishResult, hresultFuel, hresultBound, hfinishTrace⟩
    have hexponentialResult' :
      (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
        key hint (n - hint) 0 1).result = some exponential := by
      simpa only [maxOffset] using hexponentialResult
    have hbranchResult :
      ((gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
        key hint (n - hint) 0 1).bind fun current =>
        let currentCapped := min current.offset (n - hint)
        finishGallopLeftTraced? (n + 1) state.key_compare source key n
          (Int.ofNat current.lastOffset + Int.ofNat hint)
          (Int.ofNat currentCapped + Int.ofNat hint)
          current.fuelExhausted).result = some result := by
      simp only [TraceResult.bind, hexponentialResult']
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishResult
    have hbranchTrace : GallopTraceSafe
      ((gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
        key hint (n - hint) 0 1).bind fun current =>
        let currentCapped := min current.offset (n - hint)
        finishGallopLeftTraced? (n + 1) state.key_compare source key n
          (Int.ofNat current.lastOffset + Int.ofNat hint)
          (Int.ofNat currentCapped + Int.ofNat hint)
          current.fuelExhausted) := by
      apply gallopTraceSafe_bind _ _ exponential hexponentialResult
        hexponentialTrace
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishTrace
    refine ⟨result, ?_, hresultFuel, hresultBound, ?_⟩
    · simp only [gallopLeftTraced?, if_pos hinput, TraceResult.bind,
      hhintedResult, if_pos hcompare]
      exact hbranchResult
    · have hwhole := gallopTraceSafe_bind
      (source.readTraced? (Int.ofNat hint))
      (fun current =>
        if iflt state.key_compare current.key key then
          (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
            key hint (n - hint) 0 1).bind fun exponentialCurrent =>
              let currentCapped := min exponentialCurrent.offset (n - hint)
              finishGallopLeftTraced? (n + 1) state.key_compare source key n
                (Int.ofNat exponentialCurrent.lastOffset + Int.ofNat hint)
                (Int.ofNat currentCapped + Int.ofNat hint)
                exponentialCurrent.fuelExhausted
        else
          (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
            key hint (hint + 1) 0 1).bind fun exponentialCurrent =>
              let currentCapped := min exponentialCurrent.offset (hint + 1)
              finishGallopLeftTraced? (n + 1) state.key_compare source key n
                (Int.ofNat hint - Int.ofNat currentCapped)
                (Int.ofNat hint - Int.ofNat exponentialCurrent.lastOffset)
                exponentialCurrent.fuelExhausted)
      hinted hhintedResult hhintedSafe
      (by simpa only [if_pos hcompare] using hbranchTrace)
      rwa [gallopLeftTraced?, if_pos hinput]
  · let maxOffset := hint + 1
    have hmaxPositive : 0 < maxOffset := by
      dsimp [maxOffset]
      omega
    have hwindow : maxOffset ≤ hint + 1 := by rfl
    have hbudget : maxOffset ≤ (n + 1) + 1 := by
      dsimp [maxOffset]
      omega
    rcases gallopLeftLeftExponential_safe (n + 1) state.key_compare source
      key hint maxOffset 0 1 n hvalid hlive hhint hwindow hnmax (by omega)
      (by omega) hmaxPositive hbudget with
      ⟨exponential, hexponentialResult, hexponentialFuel,
        hexponentialOrder, hexponentialMax, hexponentialTrace⟩
    let capped := min exponential.offset maxOffset
    have hexponentialCapped : exponential.lastOffset < capped := by
      dsimp [capped]
      omega
    have hcappedMax : capped ≤ maxOffset := Nat.min_le_right _ _
    have hlast :
      (-1 : Int) ≤ Int.ofNat hint - Int.ofNat capped := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have horder :
      Int.ofNat hint - Int.ofNat capped <
        Int.ofNat hint - Int.ofNat exponential.lastOffset := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupper :
      Int.ofNat hint - Int.ofNat exponential.lastOffset ≤
        Int.ofNat n := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hlowerNonnegative :
      0 ≤ Int.ofNat hint - Int.ofNat capped + 1 := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have hupperNonnegative :
      0 ≤ Int.ofNat hint - Int.ofNat exponential.lastOffset := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hexponentialMax
      omega
    rcases finishGallopLeft_safe (n + 1) state.key_compare source key n
      (Int.ofNat hint - Int.ofNat capped)
      (Int.ofNat hint - Int.ofNat exponential.lastOffset) hvalid hlive
      hlast horder hupper hlowerNonnegative hupperNonnegative (by omega) with
      ⟨result, hfinishResult, hresultFuel, hresultBound, hfinishTrace⟩
    have hexponentialResult' :
      (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
        key hint (hint + 1) 0 1).result = some exponential := by
      simpa only [maxOffset] using hexponentialResult
    have hbranchResult :
      ((gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
        key hint (hint + 1) 0 1).bind fun current =>
        let currentCapped := min current.offset (hint + 1)
        finishGallopLeftTraced? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat currentCapped)
          (Int.ofNat hint - Int.ofNat current.lastOffset)
          current.fuelExhausted).result = some result := by
      simp only [TraceResult.bind, hexponentialResult']
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishResult
    have hbranchTrace : GallopTraceSafe
      ((gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
        key hint (hint + 1) 0 1).bind fun current =>
        let currentCapped := min current.offset (hint + 1)
        finishGallopLeftTraced? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat currentCapped)
          (Int.ofNat hint - Int.ofNat current.lastOffset)
          current.fuelExhausted) := by
      apply gallopTraceSafe_bind _ _ exponential hexponentialResult
        hexponentialTrace
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishTrace
    refine ⟨result, ?_, hresultFuel, hresultBound, ?_⟩
    · simp only [gallopLeftTraced?, if_pos hinput, TraceResult.bind,
      hhintedResult, if_neg hcompare]
      exact hbranchResult
    · have hwhole := gallopTraceSafe_bind
      (source.readTraced? (Int.ofNat hint))
      (fun current =>
        if iflt state.key_compare current.key key then
          (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
            key hint (n - hint) 0 1).bind fun exponentialCurrent =>
              let currentCapped := min exponentialCurrent.offset (n - hint)
              finishGallopLeftTraced? (n + 1) state.key_compare source key n
                (Int.ofNat exponentialCurrent.lastOffset + Int.ofNat hint)
                (Int.ofNat currentCapped + Int.ofNat hint)
                exponentialCurrent.fuelExhausted
        else
          (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
            key hint (hint + 1) 0 1).bind fun exponentialCurrent =>
              let currentCapped := min exponentialCurrent.offset (hint + 1)
              finishGallopLeftTraced? (n + 1) state.key_compare source key n
                (Int.ofNat hint - Int.ofNat currentCapped)
                (Int.ofNat hint - Int.ofNat exponentialCurrent.lastOffset)
                exponentialCurrent.fuelExhausted)
      hinted hhintedResult hhintedSafe
      (by simpa only [if_neg hcompare] using hbranchTrace)
      rwa [gallopLeftTraced?, if_pos hinput]

end CPythonListsort

namespace CPythonListsort

/--
[gallopDualState_keyCompare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopDualState_keyCompare
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (gallopDualState state).key_compare = gallopComparatorDual state.key_compare :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_eq_left_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRight_eq_left_dual
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat) :
-- imply
  gallopRightTraced? state source key n hint = gallopLeftTraced? (gallopDualState state) source key n hint := by
-- proof
  simp only [gallopRightTraced?, gallopLeftTraced?]
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · rw [if_pos hinput, if_pos hinput]
    apply congrArg (TraceResult.bind (source.readTraced? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : state.key_compare key hinted.key = true
    · simp [gallopDualState, gallopComparatorDual, hcompare,
      gallopRightLeft_eq_leftLeft_dual,
      finishGallopRightTraced?, finishGallopLeftTraced?,
      gallopRightBinary_eq_leftBinary_dual]
    · have hfalse : state.key_compare key hinted.key = false :=
      Bool.eq_false_of_not_eq_true hcompare
      simp [gallopDualState, gallopComparatorDual, hfalse,
        gallopRightRight_eq_leftRight_dual,
        finishGallopRightTraced?, finishGallopLeftTraced?,
        gallopRightBinary_eq_leftBinary_dual]
  · rw [if_neg hinput, if_neg hinput]

end CPythonListsort

namespace CPythonListsort

/--
[gallopRightFromSource_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopSafety.lean)
-/
@[path]
lemma gallopRightFromSource_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, (gallopRightTraced? state source key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ GallopTraceSafe (gallopRightTraced? state source key n hint) := by
-- proof
  rw [gallopRight_eq_left_dual]
  exact gallopLeftFromSource_safe (gallopDualState state) source key n hint
    hvalid hlive hn hhint hnmax

end CPythonListsort


-- created on 2026-10-23
