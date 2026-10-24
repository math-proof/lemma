import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.SortSliceSafety
open CPythonListsort


namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_sameBacking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_sameBacking
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  memmoveFromTraced? valuesPresent destination .sameBacking dst src count = memmoveTraced? valuesPresent destination dst src count := by
-- proof
  rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyKeysFromTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyKeysFromTraced
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyKeysFromTraced? destination source dst src).erase = destination.copyFrom? source dst src := by
-- proof
  simp [copyKeysFromTraced?, copyFrom?, TraceResult.erase_bind]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyValuesFromTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyValuesFromTraced
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyValuesFromTraced? destination source dst src).erase = destination.copyFrom? source dst src := by
-- proof
  simp [copyValuesFromTraced?, copyFrom?, TraceResult.erase_bind]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyFromTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyFromTraced
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyFromTraced? valuesPresent destination source dst src).erase = destination.copyFrom? source dst src := by
-- proof
  unfold copyFromTraced?
  rw [TraceResult.erase_bind, erase_copyKeysFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    cases valuesPresent <;> simp [hcopy]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyTraced
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyTraced? valuesPresent slice dst src).erase = slice.copy? dst src := by
-- proof
  simp [copyTraced?, copy?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyFromIncrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyFromIncrTraced
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyFromIncrTraced? valuesPresent destination source dst src).erase = destination.copyFromIncr? source dst src := by
-- proof
  simp only [copyFromIncrTraced?, TraceResult.erase_map,
    erase_copyFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    simp [copyFromIncr?, hcopy]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyFromDecrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyFromDecrTraced
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyFromDecrTraced? valuesPresent destination source dst src).erase = destination.copyFromDecr? source dst src := by
-- proof
  simp only [copyFromDecrTraced?, TraceResult.erase_map,
    erase_copyFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    simp [copyFromDecr?, hcopy]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyIncrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyIncrTraced
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyIncrTraced? valuesPresent slice dst src).erase = slice.copyIncr? dst src := by
-- proof
  simp [copyIncrTraced?, copyIncr?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_copyDecrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_copyDecrTraced
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (copyDecrTraced? valuesPresent slice dst src).erase = slice.copyDecr? dst src := by
-- proof
  simp [copyDecrTraced?, copyDecr?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memcpyKeysTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memcpyKeysTraced
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memcpyKeysTraced? count destination source dst src).erase = memcpyCore? count destination source dst src := by
-- proof
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
    simp [memcpyKeysTraced?, memcpyCore?, ih]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memcpyValuesTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memcpyValuesTraced
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memcpyValuesTraced? count destination source dst src).erase = memcpyCore? count destination source dst src := by
-- proof
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
    simp [memcpyValuesTraced?, memcpyCore?, ih]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memcpyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memcpyTraced
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {dst src : Int} :
-- imply
  (memcpyTraced? valuesPresent count destination source dst src).erase = memcpy? count destination source dst src := by
-- proof
  unfold memcpyTraced? memcpy?
  split
  · rw [TraceResult.erase_bind, erase_memcpyKeysTraced]
    cases hcopy : memcpyCore? count destination source.store dst src <;>
      cases valuesPresent <;> simp [hcopy]
  · rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveForwardKeysTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveForwardKeysTraced
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memmoveForwardKeysTraced? count slice dst src).erase = memmoveForward? count slice dst src := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp [memmoveForwardKeysTraced?, memmoveForward?, ih, copy?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveForwardValuesTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveForwardValuesTraced
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memmoveForwardValuesTraced? count slice dst src).erase = memmoveForward? count slice dst src := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp [memmoveForwardValuesTraced?, memmoveForward?, ih, copy?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveBackwardKeysTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveBackwardKeysTraced
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memmoveBackwardKeysTraced? count slice dst src).erase = memmoveBackward? count slice dst src := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp [memmoveBackwardKeysTraced?, memmoveBackward?, ih, copy?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveBackwardValuesTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveBackwardValuesTraced
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int} :
-- imply
  (memmoveBackwardValuesTraced? count slice dst src).erase = memmoveBackward? count slice dst src := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp [memmoveBackwardValuesTraced?, memmoveBackward?, ih, copy?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveTraced
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  (memmoveTraced? valuesPresent slice dst src count).erase = slice.memmove? dst src count := by
-- proof
  cases hdir : memmoveDirection dst src with
  | forward =>
    simp only [memmoveTraced?, memmove?, hdir, TraceResult.erase_bind,
      erase_memmoveForwardKeysTraced]
    cases hmove : memmoveForward? count slice dst src <;>
      cases valuesPresent <;> simp [hmove]
  | backward =>
    simp only [memmoveTraced?, memmove?, hdir, TraceResult.erase_bind,
      erase_memmoveBackwardKeysTraced]
    cases hmove : memmoveBackward? count slice dst src <;>
      cases valuesPresent <;> simp [hmove]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_memmoveFromTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_memmoveFromTraced
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {dst src : Int}
  {count : Nat} :
-- imply
  (memmoveFromTraced? valuesPresent destination source dst src count).erase = memmoveFrom? destination source dst src count := by
-- proof
  cases source with
  | sameBacking => simp [memmoveFromTraced?, memmoveFrom?]
  | distinctBacking source =>
    simp only [memmoveFromTraced?, memmoveFrom?, TraceResult.erase_bind,
      erase_memcpyKeysTraced]
    cases hmove : memcpyCore? count destination source dst src <;>
      cases valuesPresent <;> simp [hmove]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[erase_advanceTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma erase_advanceTraced
  {valuesPresent : Bool}
  {index amount : Int} :
-- imply
  (advanceTraced valuesPresent index amount).erase = some (advance index amount) := by
-- proof
  rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[read_eq_some_of_indexInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma read_eq_some_of_indexInBounds
  {slice : SortSlice κ ν}
  {index : Int}
-- given
  (h : IndexInBounds slice index) :
-- imply
  ∃ entry, slice.read? index = some entry := by
-- proof
  obtain ⟨hnonnegative, hupper⟩ := h
  have hnat : index.toNat < slice.entries.size :=
    (Int.toNat_lt hnonnegative).2 hupper
  refine ⟨slice.entries[index.toNat], ?_⟩
  simp [read?, hnonnegative, Array.getElem?_eq_getElem hnat]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_eq_some_of_indexInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma write_eq_some_of_indexInBounds
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (h : IndexInBounds slice index) :
-- imply
  ∃ updated, slice.write? index entry = some updated := by
-- proof
  obtain ⟨hnonnegative, hupper⟩ := h
  have hnat : index.toNat < slice.entries.size :=
    (Int.toNat_lt hnonnegative).2 hupper
  refine ⟨{ entries := slice.entries.set index.toNat entry }, ?_⟩
  simp [write?, hnonnegative, hnat]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[falseMode_somePayload_violates_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma falseMode_somePayload_violates_invariant
  {key : κ}
  {value : ν} :
-- imply
  ¬ ValuesModeInvariant false ({ entries := #[{ key := key, value := some value }] } : SortSlice κ ν) := by
-- proof
  intro hinvariant
  have hentry := hinvariant 0 (by simp)
  simp [EntryMatchesValuesMode] at hentry

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.read_matches_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.read_matches_of_eq_some
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hread : slice.read? index = some entry) :
-- imply
  EntryMatchesValuesMode valuesPresent entry := by
-- proof
  unfold read? at hread
  split at hread
  · rename_i hnonnegative
    have hindex : index.toNat < slice.entries.size := by
      by_contra hnot
      have hout : slice.entries[index.toNat]? = none :=
        Array.getElem?_eq_none (Nat.le_of_not_gt hnot)
      simp [hout] at hread
    rw [Array.getElem?_eq_getElem hindex] at hread
    simp only [Option.some.injEq] at hread
    subst entry
    exact hinvariant index.toNat hindex
  · simp at hread

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.write_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.write_preserved_of_eq_some
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hentry : EntryMatchesValuesMode valuesPresent entry)
  (hwrite : slice.write? index entry = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  unfold write? at hwrite
  split at hwrite
  · dsimp only at hwrite
    split at hwrite
    · rename_i hnonnegative hinBounds
      simp only [Option.some.injEq] at hwrite
      subst updated
      intro other hother
      rw [Array.getElem_set]
      split
      · exact hentry
      · apply hinvariant
    · contradiction
  · contradiction

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copyFrom_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copyFrom_preserved_of_eq_some
  {valuesPresent : Bool}
  {destination source updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hcopy : destination.copyFrom? source dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  simp only [copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact hdestination.write_preserved_of_eq_some
      (hsource.read_matches_of_eq_some hread) hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copy_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copy_preserved_of_eq_some
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hcopy : slice.copy? dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated :=
-- proof
  hinvariant.copyFrom_preserved_of_eq_some hinvariant hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copyFromIncr_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copyFromIncr_preserved_of_eq_some
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hcopy : destination.copyFromIncr? source dst src = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  simp only [copyFromIncr?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i updated hstep
    have hresult :
      ({ slice := updated, dst := dst + 1, src := src + 1 } :
        CursorResult κ ν) = result := by
      simpa using hcopy
    rw [← hresult]
    exact hdestination.copyFrom_preserved_of_eq_some hsource hstep

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copyFromDecr_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copyFromDecr_preserved_of_eq_some
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hcopy : destination.copyFromDecr? source dst src = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  simp only [copyFromDecr?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i updated hstep
    have hresult :
      ({ slice := updated, dst := dst - 1, src := src - 1 } :
        CursorResult κ ν) = result := by
      simpa using hcopy
    rw [← hresult]
    exact hdestination.copyFrom_preserved_of_eq_some hsource hstep

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copyIncr_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copyIncr_preserved_of_eq_some
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hcopy : slice.copyIncr? dst src = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice :=
-- proof
  hinvariant.copyFromIncr_preserved_of_eq_some hinvariant hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.copyDecr_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.copyDecr_preserved_of_eq_some
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hcopy : slice.copyDecr? dst src = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice :=
-- proof
  hinvariant.copyFromDecr_preserved_of_eq_some hinvariant hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memcpyCore_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memcpyCore_preserved_of_eq_some
  {valuesPresent : Bool}
  {count : Nat}
  {destination source updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hcopy : memcpyCore? count destination source dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  induction count generalizing destination dst src with
  | zero =>
    simp only [memcpyCore?, Option.some.injEq] at hcopy
    subst updated
    exact hdestination
  | succ count ih =>
    simp only [memcpyCore?, bind, Option.bind] at hcopy
    split at hcopy
    · simp at hcopy
    · rename_i first hfirst
      exact ih
        (hdestination.copyFrom_preserved_of_eq_some hsource hfirst)
        hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memcpy_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memcpy_preserved_of_eq_some
  {valuesPresent : Bool}
  {count : Nat}
  {destination updated : SortSlice κ ν}
  {source : MemcpySource destination}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hcopy : memcpy? count destination source dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  unfold memcpy? at hcopy
  split at hcopy
  · exact hdestination.memcpyCore_preserved_of_eq_some count hsource hcopy
  · simp at hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memmoveForward_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memmoveForward_preserved_of_eq_some
  {valuesPresent : Bool}
  {count : Nat}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hmove : memmoveForward? count slice dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    simp only [memmoveForward?, Option.some.injEq] at hmove
    subst updated
    exact hinvariant
  | succ count ih =>
    simp only [memmoveForward?, bind, Option.bind] at hmove
    split at hmove
    · simp at hmove
    · rename_i first hfirst
      exact ih (hinvariant.copy_preserved_of_eq_some hfirst) hmove

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memmoveBackward_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memmoveBackward_preserved_of_eq_some
  {valuesPresent : Bool}
  {count : Nat}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hmove : memmoveBackward? count slice dst src = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    simp only [memmoveBackward?, Option.some.injEq] at hmove
    subst updated
    exact hinvariant
  | succ count ih =>
    simp only [memmoveBackward?, bind, Option.bind] at hmove
    split at hmove
    · simp at hmove
    · rename_i first hfirst
      exact ih (hinvariant.copy_preserved_of_eq_some hfirst) hmove

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memmove_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memmove_preserved_of_eq_some
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hmove : slice.memmove? dst src count = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  unfold memmove? at hmove
  split at hmove
  · exact hinvariant.memmoveForward_preserved_of_eq_some count hmove
  · exact hinvariant.memmoveBackward_preserved_of_eq_some count hmove

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ValuesModeInvariant.memmoveFrom_preserved_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma ValuesModeInvariant.memmoveFrom_preserved_of_eq_some
  {valuesPresent : Bool}
  {destination updated : SortSlice κ ν}
  {source : MemmoveSource destination}
  {dst src : Int}
  {count : Nat}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hmove : memmoveFrom? destination source dst src count = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  cases source with
  | sameBacking =>
    exact hdestination.memmove_preserved_of_eq_some hmove
  | distinctBacking source =>
    exact hdestination.memcpyCore_preserved_of_eq_some count hsource hmove

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {destination source updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hresult : (copyFromTraced? valuesPresent destination source dst src).result = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  apply hdestination.copyFrom_preserved_of_eq_some hsource
  rwa [← erase_copyFromTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hresult : (copyTraced? valuesPresent slice dst src).result = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  apply hinvariant.copy_preserved_of_eq_some
  rwa [← erase_copyTraced valuesPresent slice dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncrTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromIncrTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hresult : (copyFromIncrTraced? valuesPresent destination source dst src).result = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  apply hdestination.copyFromIncr_preserved_of_eq_some hsource
  rwa [← erase_copyFromIncrTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecrTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromDecrTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hresult : (copyFromDecrTraced? valuesPresent destination source dst src).result = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  apply hdestination.copyFromDecr_preserved_of_eq_some hsource
  rwa [← erase_copyFromDecrTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyIncrTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyIncrTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hresult : (copyIncrTraced? valuesPresent slice dst src).result = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  exact copyFromIncrTraced_valuesModeInvariant valuesPresent slice slice dst src
    result hinvariant hinvariant hresult

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyDecrTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyDecrTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hresult : (copyDecrTraced? valuesPresent slice dst src).result = some result) :
-- imply
  ValuesModeInvariant valuesPresent result.slice := by
-- proof
  exact copyFromDecrTraced_valuesModeInvariant valuesPresent slice slice dst src
    result hinvariant hinvariant hresult

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hresult : (memcpyTraced? valuesPresent count destination source dst src).result = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  apply hdestination.memcpy_preserved_of_eq_some count source hsource
  rwa [← erase_memcpyTraced valuesPresent count destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hresult : (memmoveTraced? valuesPresent slice dst src count).result = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  apply hinvariant.memmove_preserved_of_eq_some
  rwa [← erase_memmoveTraced valuesPresent slice dst src count]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_valuesModeInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_valuesModeInvariant
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hresult : (memmoveFromTraced? valuesPresent destination source dst src count).result = some updated) :
-- imply
  ValuesModeInvariant valuesPresent updated := by
-- proof
  apply hdestination.memmoveFrom_preserved_of_eq_some source hsource
  rwa [← erase_memmoveFromTraced valuesPresent destination source dst src count]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyKeysFromTraced_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyKeysFromTraced_accesses
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (_hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyKeysFromTraced? destination source dst src).trace.accesses = keyCopyAccesses destination.entries.size source.entries.size dst src := by
-- proof
  obtain ⟨entry, hread⟩ := read_eq_some_of_indexInBounds source src hsrc
  simp [copyKeysFromTraced?, TraceResult.trace_bind,
    TraceResult.sortSliceKeysRead?, TraceResult.sortSliceKeysWrite?,
    hread, TraceResult.captureAccess, AccessTrace.singletonAccess,
    AccessTrace.compose, keyCopyAccesses]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyValuesFromTraced_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyValuesFromTraced_accesses
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (_hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyValuesFromTraced? destination source dst src).trace.accesses = valuesCopyAccesses destination.entries.size source.entries.size dst src := by
-- proof
  obtain ⟨entry, hread⟩ := read_eq_some_of_indexInBounds source src hsrc
  simp [copyValuesFromTraced?, TraceResult.trace_bind,
    TraceResult.sortSliceValuesRead?, TraceResult.sortSliceValuesWrite?,
    hread, TraceResult.captureAccess, AccessTrace.singletonAccess,
    AccessTrace.compose, valuesCopyAccesses]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_accesses
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromTraced? valuesPresent destination source dst src).trace.accesses = keyCopyAccesses destination.entries.size source.entries.size dst src ++ if valuesPresent then valuesCopyAccesses destination.entries.size source.entries.size dst src else [] := by
-- proof
  obtain ⟨entry, hread⟩ := read_eq_some_of_indexInBounds source src hsrc
  rcases write_eq_some_of_indexInBounds destination dst entry hdst with
    ⟨updated, hwrite⟩
  have hcopy : destination.copyFrom? source dst src = some updated := by
    simp [copyFrom?, hread, hwrite]
  have hkeyResult :
    (copyKeysFromTraced? destination source dst src).result = some updated := by
    change (copyKeysFromTraced? destination source dst src).erase = some updated
    rwa [erase_copyKeysFromTraced]
  unfold copyFromTraced?
  rw [TraceResult.trace_bind, hkeyResult]
  cases valuesPresent <;>
    simp [copyKeysFromTraced_accesses destination source dst src hdst hsrc,
      copyValuesFromTraced_accesses destination source dst src hdst hsrc,
      TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncrTraced_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromIncrTraced_accesses
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromIncrTraced? valuesPresent destination source dst src).trace.accesses = keyCopyAccesses destination.entries.size source.entries.size dst src ++ if valuesPresent then valuesCopyAccesses destination.entries.size source.entries.size dst src else [] := by
-- proof
  simpa [copyFromIncrTraced?, TraceResult.map] using
    copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecrTraced_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromDecrTraced_accesses
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromDecrTraced? valuesPresent destination source dst src).trace.accesses = keyCopyAccesses destination.entries.size source.entries.size dst src ++ if valuesPresent then valuesCopyAccesses destination.entries.size source.entries.size dst src else [] := by
-- proof
  simpa [copyFromDecrTraced?, TraceResult.map] using
    copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromTraced? valuesPresent destination source dst src).trace := by
-- proof
  rw [AccessTrace.allAccessesInBounds]
  rw [copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc]
  obtain ⟨hdst0, hdstN⟩ := hdst
  obtain ⟨hsrc0, hsrcN⟩ := hsrc
  cases valuesPresent
  · simp only [Bool.false_eq_true, if_false, List.append_nil]
    intro event hevent
    simp only [keyCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
      at hevent
    obtain rfl | rfl := hevent
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩
  · simp only [if_true]
    intro event hevent
    simp only [keyCopyAccesses, valuesCopyAccesses, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hevent
    obtain (rfl | rfl) | (rfl | rfl) := hevent
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src) :
-- imply
  (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
-- proof
  exact copyFromTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncrTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromIncrTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromIncrTraced? valuesPresent destination source dst src).trace := by
-- proof
  simpa [copyFromIncrTraced?, TraceResult.map] using
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecrTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromDecrTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyFromDecrTraced? valuesPresent destination source dst src).trace := by
-- proof
  simpa [copyFromDecrTraced?, TraceResult.map] using
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyIncrTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyIncrTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src) :
-- imply
  (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
-- proof
  exact copyFromIncrTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyDecrTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyDecrTraced_allAccessesInBounds
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src) :
-- imply
  (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
-- proof
  exact copyFromDecrTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyKeysFromTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyKeysFromTraced_allAccessesInBounds
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyKeysFromTraced? destination source dst src).trace := by
-- proof
  rw [AccessTrace.allAccessesInBounds,
    copyKeysFromTraced_accesses destination source dst src hdst hsrc]
  intro event hevent
  simp only [keyCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
    at hevent
  obtain rfl | rfl := hevent
  · simpa [IndexInBounds, AccessEvent.InBounds] using hsrc
  · simpa [IndexInBounds, AccessEvent.InBounds] using hdst

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyValuesFromTraced_allAccessesInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyValuesFromTraced_allAccessesInBounds
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  (copyValuesFromTraced? destination source dst src).trace := by
-- proof
  rw [AccessTrace.allAccessesInBounds,
    copyValuesFromTraced_accesses destination source dst src hdst hsrc]
  intro event hevent
  simp only [valuesCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
    at hevent
  obtain rfl | rfl := hevent
  · simpa [IndexInBounds, AccessEvent.InBounds] using hsrc
  · simpa [IndexInBounds, AccessEvent.InBounds] using hdst

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFrom_eq_some_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFrom_eq_some_of_bounds
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  ∃ updated, destination.copyFrom? source dst src = some updated := by
-- proof
  obtain ⟨entry, hread⟩ := read_eq_some_of_indexInBounds source src hsrc
  rcases write_eq_some_of_indexInBounds destination dst entry hdst with
    ⟨updated, hwrite⟩
  exact ⟨updated, by simp [copyFrom?, hread, hwrite]⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[RangeInBounds.head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma RangeInBounds.head
  {slice : SortSlice κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : RangeInBounds slice start (count + 1)) :
-- imply
  IndexInBounds slice start := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[RangeInBounds.tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma RangeInBounds.tail
  {slice : SortSlice κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : RangeInBounds slice start (count + 1)) :
-- imply
  RangeInBounds slice (start + 1) count := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · omega
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[RangeInBounds.prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma RangeInBounds.prefix
  {slice : SortSlice κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : RangeInBounds slice start (count + 1)) :
-- imply
  RangeInBounds slice start count := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[RangeInBounds.last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma RangeInBounds.last
  {slice : SortSlice κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : RangeInBounds slice start (count + 1)) :
-- imply
  IndexInBounds slice (start + Int.ofNat count) := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · exact add_nonneg hstart (Int.natCast_nonneg count)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[RangeInBounds.of_size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma RangeInBounds.of_size_eq
  {first second : SortSlice κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : RangeInBounds first start count)
  (hsize : second.entries.size = first.entries.size) :
-- imply
  RangeInBounds second start count := by
-- proof
  simpa [RangeInBounds, hsize] using h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[IndexInBounds.of_size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma IndexInBounds.of_size_eq
  {first second : SortSlice κ ν}
  {index : Int}
-- given
  (h : IndexInBounds first index)
  (hsize : second.entries.size = first.entries.size) :
-- imply
  IndexInBounds second index := by
-- proof
  simpa [IndexInBounds, hsize] using h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[IndexInBounds.cursorInRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma IndexInBounds.cursorInRange
  {slice : SortSlice κ ν}
  {index : Int}
-- given
  (h : IndexInBounds slice index) :
-- imply
  CursorInRange slice index :=
-- proof
⟨h.1, h.2.le⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[IndexInBounds.increment_cursorInRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma IndexInBounds.increment_cursorInRange
  {slice : SortSlice κ ν}
  {index : Int}
-- given
  (h : IndexInBounds slice index) :
-- imply
  CursorInRange slice (index + 1) := by
-- proof
  obtain ⟨hlower, hupper⟩ := h
  constructor <;> omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[IndexInBounds.decrement_cursorInRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma IndexInBounds.decrement_cursorInRange
  {slice : SortSlice κ ν}
  {index : Int}
-- given
  (h : IndexInBounds slice index)
  (hpositive : 0 < index) :
-- imply
  CursorInRange slice (index - 1) := by
-- proof
  obtain ⟨_, hupper⟩ := h
  constructor <;> omega

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[CursorInRange.of_size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma CursorInRange.of_size_eq
  {first second : SortSlice κ ν}
  {cursor : Int}
-- given
  (h : CursorInRange first cursor)
  (hsize : second.entries.size = first.entries.size) :
-- imply
  CursorInRange second cursor := by
-- proof
  simpa [CursorInRange, hsize] using h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyKeysTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyKeysTraced_safe
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source src count) :
-- imply
  ∃ updated, (memcpyKeysTraced? count destination source dst src).result = some updated ∧ (memcpyKeysTraced? count destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size := by
-- proof
  induction count generalizing destination dst src with
  | zero =>
    exact ⟨destination, rfl, by simp [memcpyKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstHead := hdst.head
    have hsrcHead := hsrc.head
    rcases copyFrom_eq_some_of_bounds destination source dst src hdstHead
      hsrcHead with ⟨first, hcopy⟩
    have hfirst :
      (copyKeysFromTraced? destination source dst src).result = some first := by
      change (copyKeysFromTraced? destination source dst src).erase = some first
      rwa [erase_copyKeysFromTraced]
    have hfirstSize : first.entries.size = destination.entries.size :=
      copyFrom_entries_size_of_eq_some destination source first dst src hcopy
    have hdstTail : RangeInBounds first (dst + 1) count :=
      hdst.tail.of_size_eq hfirstSize
    have hsrcTail : RangeInBounds source (src + 1) count := hsrc.tail
    rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memcpyKeysTraced?, TraceResult.bind, hfirst] using hrest
    · have htrace :
      (memcpyKeysTraced? (count + 1) destination source dst src).trace =
        (copyKeysFromTraced? destination source dst src).trace.compose
          (memcpyKeysTraced? count first source (dst + 1) (src + 1)).trace := by
      simp [memcpyKeysTraced?, TraceResult.trace_bind, hfirst]
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyKeysFromTraced_allAccessesInBounds destination source dst src
        hdstHead hsrcHead, hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyValuesTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyValuesTraced_safe
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source src count) :
-- imply
  ∃ updated, (memcpyValuesTraced? count destination source dst src).result = some updated ∧ (memcpyValuesTraced? count destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size := by
-- proof
  induction count generalizing destination dst src with
  | zero =>
    exact ⟨destination, rfl, by simp [memcpyValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstHead := hdst.head
    have hsrcHead := hsrc.head
    rcases copyFrom_eq_some_of_bounds destination source dst src hdstHead
      hsrcHead with ⟨first, hcopy⟩
    have hfirst :
      (copyValuesFromTraced? destination source dst src).result = some first := by
      change (copyValuesFromTraced? destination source dst src).erase = some first
      rwa [erase_copyValuesFromTraced]
    have hfirstSize : first.entries.size = destination.entries.size :=
      copyFrom_entries_size_of_eq_some destination source first dst src hcopy
    have hdstTail : RangeInBounds first (dst + 1) count :=
      hdst.tail.of_size_eq hfirstSize
    have hsrcTail : RangeInBounds source (src + 1) count := hsrc.tail
    rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memcpyValuesTraced?, TraceResult.bind, hfirst] using hrest
    · have htrace :
      (memcpyValuesTraced? (count + 1) destination source dst src).trace =
        (copyValuesFromTraced? destination source dst src).trace.compose
          (memcpyValuesTraced? count first source (dst + 1) (src + 1)).trace := by
      simp [memcpyValuesTraced?, TraceResult.trace_bind, hfirst]
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyValuesFromTraced_allAccessesInBounds destination source dst src
        hdstHead hsrcHead, hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_safe
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {dst src : Int}
-- given
  (hadmissible : source.Admissible dst src count)
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  ∃ updated, (memcpyTraced? valuesPresent count destination source dst src).result = some updated ∧ (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size := by
-- proof
  rcases memcpyKeysTraced_safe count destination source.store dst src hdst hsrc with
    ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
  cases valuesPresent with
  | false =>
    refine ⟨keyResult, ?_, ?_, hkeysSize⟩
    · simp [memcpyTraced?, hadmissible, TraceResult.bind, TraceResult.pure,
      hkeys]
    · simpa [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys,
      TraceResult.pure] using hkeysBounds
  | true =>
    rcases memcpyValuesTraced_safe count destination source.store dst src hdst hsrc with
      ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
    refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
    · simpa [memcpyTraced?, hadmissible, TraceResult.bind, hkeys] using hvalues
    · have htrace :
      (memcpyTraced? true count destination source dst src).trace =
        (memcpyKeysTraced? count destination source.store dst src).trace.compose
          (memcpyValuesTraced? count destination source.store dst src).trace := by
      simp [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys]
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨hkeysBounds, hvaluesBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_phase_order
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {dst src : Int}
-- given
  (hadmissible : source.Admissible dst src count)
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  (memcpyTraced? valuesPresent count destination source dst src).trace.accesses = (memcpyKeysTraced? count destination source.store dst src).trace.accesses ++ if valuesPresent then (memcpyValuesTraced? count destination source.store dst src).trace.accesses else [] := by
-- proof
  rcases memcpyKeysTraced_safe count destination source.store dst src hdst hsrc with
    ⟨keyResult, hkeys, _, _⟩
  cases valuesPresent <;>
    simp [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys,
      TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_distinctBacking_values_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_distinctBacking_values_phase_order
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source src count) :
-- imply
  (memcpyTraced? true count destination (.distinctBacking source) dst src).trace.accesses = (memcpyKeysTraced? count destination source dst src).trace.accesses ++ (memcpyValuesTraced? count destination source dst src).trace.accesses := by
-- proof
  simpa [MemcpySource.store] using
    memcpyTraced_phase_order true count destination (.distinctBacking source)
      dst src (by simp [MemcpySource.Admissible]) hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveForwardKeysTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveForwardKeysTraced_safe
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveForwardKeysTraced? count slice dst src).result = some updated ∧ (memmoveForwardKeysTraced? count slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    exact ⟨slice, rfl, by simp [memmoveForwardKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstHead := hdst.head
    have hsrcHead := hsrc.head
    rcases copyFrom_eq_some_of_bounds slice slice dst src hdstHead hsrcHead with
      ⟨first, hcopy⟩
    have hfirst :
      (copyKeysFromTraced? slice slice dst src).result = some first := by
      change (copyKeysFromTraced? slice slice dst src).erase = some first
      rwa [erase_copyKeysFromTraced]
    have hfirstSize : first.entries.size = slice.entries.size :=
      copyFrom_entries_size_of_eq_some slice slice first dst src hcopy
    have hdstTail : RangeInBounds first (dst + 1) count :=
      hdst.tail.of_size_eq hfirstSize
    have hsrcTail : RangeInBounds first (src + 1) count :=
      hsrc.tail.of_size_eq hfirstSize
    rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memmoveForwardKeysTraced?, TraceResult.bind, hfirst] using hrest
    · have htrace :
      (memmoveForwardKeysTraced? (count + 1) slice dst src).trace =
        (copyKeysFromTraced? slice slice dst src).trace.compose
          (memmoveForwardKeysTraced? count first (dst + 1) (src + 1)).trace := by
      simp [memmoveForwardKeysTraced?, TraceResult.trace_bind, hfirst]
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyKeysFromTraced_allAccessesInBounds slice slice dst src
        hdstHead hsrcHead, hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveForwardValuesTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveForwardValuesTraced_safe
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveForwardValuesTraced? count slice dst src).result = some updated ∧ (memmoveForwardValuesTraced? count slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    exact ⟨slice, rfl, by simp [memmoveForwardValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstHead := hdst.head
    have hsrcHead := hsrc.head
    rcases copyFrom_eq_some_of_bounds slice slice dst src hdstHead hsrcHead with
      ⟨first, hcopy⟩
    have hfirst :
      (copyValuesFromTraced? slice slice dst src).result = some first := by
      change (copyValuesFromTraced? slice slice dst src).erase = some first
      rwa [erase_copyValuesFromTraced]
    have hfirstSize : first.entries.size = slice.entries.size :=
      copyFrom_entries_size_of_eq_some slice slice first dst src hcopy
    have hdstTail : RangeInBounds first (dst + 1) count :=
      hdst.tail.of_size_eq hfirstSize
    have hsrcTail : RangeInBounds first (src + 1) count :=
      hsrc.tail.of_size_eq hfirstSize
    rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memmoveForwardValuesTraced?, TraceResult.bind, hfirst] using hrest
    · have htrace :
      (memmoveForwardValuesTraced? (count + 1) slice dst src).trace =
        (copyValuesFromTraced? slice slice dst src).trace.compose
          (memmoveForwardValuesTraced? count first (dst + 1) (src + 1)).trace := by
      simp [memmoveForwardValuesTraced?, TraceResult.trace_bind, hfirst]
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyValuesFromTraced_allAccessesInBounds slice slice dst src
        hdstHead hsrcHead, hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveBackwardKeysTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveBackwardKeysTraced_safe
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveBackwardKeysTraced? count slice dst src).result = some updated ∧ (memmoveBackwardKeysTraced? count slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    exact ⟨slice, rfl, by simp [memmoveBackwardKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstLast := hdst.last
    have hsrcLast := hsrc.last
    rcases copyFrom_eq_some_of_bounds slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
      ⟨first, hcopy⟩
    have hfirst :
      (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
        (src + Int.ofNat count)).result = some first := by
      change (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
        (src + Int.ofNat count)).erase = some first
      rwa [erase_copyKeysFromTraced]
    have hfirst' :
      (copyKeysFromTraced? slice slice (dst + (count : Int))
        (src + (count : Int))).result = some first := by
      simpa using hfirst
    have hfirstSize : first.entries.size = slice.entries.size :=
      copyFrom_entries_size_of_eq_some slice slice first
        (dst + Int.ofNat count) (src + Int.ofNat count) hcopy
    have hdstPrefix : RangeInBounds first dst count :=
      hdst.prefix.of_size_eq hfirstSize
    have hsrcPrefix : RangeInBounds first src count :=
      hsrc.prefix.of_size_eq hfirstSize
    rcases ih first dst src hdstPrefix hsrcPrefix with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memmoveBackwardKeysTraced?, TraceResult.bind, hfirst'] using hrest
    · have htrace :
      (memmoveBackwardKeysTraced? (count + 1) slice dst src).trace =
        (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)).trace.compose
          (memmoveBackwardKeysTraced? count first dst src).trace := by
      simp [memmoveBackwardKeysTraced?, TraceResult.trace_bind, hfirst']
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyKeysFromTraced_allAccessesInBounds slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast,
        hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveBackwardValuesTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveBackwardValuesTraced_safe
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveBackwardValuesTraced? count slice dst src).result = some updated ∧ (memmoveBackwardValuesTraced? count slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  induction count generalizing slice dst src with
  | zero =>
    exact ⟨slice, rfl, by simp [memmoveBackwardValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
    have hdstLast := hdst.last
    have hsrcLast := hsrc.last
    rcases copyFrom_eq_some_of_bounds slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
      ⟨first, hcopy⟩
    have hfirst :
      (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
        (src + Int.ofNat count)).result = some first := by
      change (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
        (src + Int.ofNat count)).erase = some first
      rwa [erase_copyValuesFromTraced]
    have hfirst' :
      (copyValuesFromTraced? slice slice (dst + (count : Int))
        (src + (count : Int))).result = some first := by
      simpa using hfirst
    have hfirstSize : first.entries.size = slice.entries.size :=
      copyFrom_entries_size_of_eq_some slice slice first
        (dst + Int.ofNat count) (src + Int.ofNat count) hcopy
    have hdstPrefix : RangeInBounds first dst count :=
      hdst.prefix.of_size_eq hfirstSize
    have hsrcPrefix : RangeInBounds first src count :=
      hsrc.prefix.of_size_eq hfirstSize
    rcases ih first dst src hdstPrefix hsrcPrefix with
      ⟨updated, hrest, hrestBounds, hrestSize⟩
    refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
    · simpa [memmoveBackwardValuesTraced?, TraceResult.bind, hfirst'] using hrest
    · have htrace :
      (memmoveBackwardValuesTraced? (count + 1) slice dst src).trace =
        (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)).trace.compose
          (memmoveBackwardValuesTraced? count first dst src).trace := by
      simp [memmoveBackwardValuesTraced?, TraceResult.trace_bind, hfirst']
      rw [htrace, AccessTrace.allAccessesInBounds_compose]
      exact ⟨copyValuesFromTraced_allAccessesInBounds slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast,
        hrestBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveTraced_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧ (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  cases hdir : memmoveDirection dst src with
  | forward =>
    rcases memmoveForwardKeysTraced_safe count slice dst src hdst hsrc with
      ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
    cases valuesPresent with
    | false =>
      refine ⟨keyResult, ?_, ?_, hkeysSize⟩
      · simp [memmoveTraced?, hdir, TraceResult.bind, TraceResult.pure, hkeys]
      · simpa [memmoveTraced?, hdir, TraceResult.trace_bind, TraceResult.pure,
        hkeys] using hkeysBounds
    | true =>
      rcases memmoveForwardValuesTraced_safe count slice dst src hdst hsrc with
        ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
      refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
      · simpa [memmoveTraced?, hdir, TraceResult.bind, hkeys] using hvalues
      · have htrace :
        (memmoveTraced? true slice dst src count).trace =
          (memmoveForwardKeysTraced? count slice dst src).trace.compose
            (memmoveForwardValuesTraced? count slice dst src).trace := by
        simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨hkeysBounds, hvaluesBounds⟩
  | backward =>
    rcases memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
      ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
    cases valuesPresent with
    | false =>
      refine ⟨keyResult, ?_, ?_, hkeysSize⟩
      · simp [memmoveTraced?, hdir, TraceResult.bind, TraceResult.pure, hkeys]
      · simpa [memmoveTraced?, hdir, TraceResult.trace_bind, TraceResult.pure,
        hkeys] using hkeysBounds
    | true =>
      rcases memmoveBackwardValuesTraced_safe count slice dst src hdst hsrc with
        ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
      refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
      · simpa [memmoveTraced?, hdir, TraceResult.bind, hkeys] using hvalues
      · have htrace :
        (memmoveTraced? true slice dst src count).trace =
          (memmoveBackwardKeysTraced? count slice dst src).trace.compose
            (memmoveBackwardValuesTraced? count slice dst src).trace := by
        simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨hkeysBounds, hvaluesBounds⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveTraced_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveTraced_phase_order
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  (memmoveTraced? valuesPresent slice dst src count).trace.accesses = match memmoveDirection dst src with := by
-- proof
  cases hdir : memmoveDirection dst src with
  | forward =>
    rcases memmoveForwardKeysTraced_safe count slice dst src hdst hsrc with
      ⟨keyResult, hkeys, _, _⟩
    cases valuesPresent <;>
      simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys,
        TraceResult.pure, AccessTrace.compose, AccessTrace.empty]
  | backward =>
    rcases memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
      ⟨keyResult, hkeys, _, _⟩
    cases valuesPresent <;>
      simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys,
        TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_safe
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {dst src : Int}
  {count : Nat}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  ∃ updated, (memmoveFromTraced? valuesPresent destination source dst src count).result = some updated ∧ ((memmoveFromTraced? valuesPresent destination source dst src count).trace |>.allAccessesInBounds) ∧ updated.entries.size = destination.entries.size := by
-- proof
  cases source with
  | sameBacking =>
    simpa [memmoveFromTraced?, MemcpySource.store] using
      memmoveTraced_safe valuesPresent destination dst src count hdst hsrc
  | distinctBacking source =>
    simpa [memmoveFromTraced?, memcpyTraced?, MemcpySource.Admissible,
      MemcpySource.store] using
      (memcpyTraced_safe valuesPresent count destination
        (.distinctBacking source) dst src
        (by simp [MemcpySource.Admissible]) hdst hsrc)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_phase_order
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {dst src : Int}
  {count : Nat}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  (memmoveFromTraced? valuesPresent destination source dst src count).trace.accesses = match source with := by
-- proof
  cases source with
  | sameBacking =>
    simpa [memmoveFromTraced?, MemcpySource.store] using
      memmoveTraced_phase_order valuesPresent destination dst src count hdst hsrc
  | distinctBacking source =>
    simpa [memmoveFromTraced?, memcpyTraced?, MemcpySource.Admissible,
      MemcpySource.store] using
      (memcpyTraced_phase_order valuesPresent count destination
        (.distinctBacking source) dst src
        (by simp [MemcpySource.Admissible]) hdst hsrc)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_sameBacking_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_sameBacking_phase_order
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds destination src count) :
-- imply
  (memmoveFromTraced? valuesPresent destination .sameBacking dst src count).trace.accesses = match memmoveDirection dst src with := by
-- proof
  simpa [MemcpySource.store] using
    memmoveFromTraced_phase_order valuesPresent destination .sameBacking dst src
      count hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_distinctBacking_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_distinctBacking_phase_order
  {valuesPresent : Bool}
  {count : Nat}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source src count) :
-- imply
  (memmoveFromTraced? valuesPresent destination (.distinctBacking source) dst src count).trace.accesses = (memcpyKeysTraced? count destination source dst src).trace.accesses ++ if valuesPresent then (memcpyValuesTraced? count destination source dst src).trace.accesses else [] := by
-- proof
  simpa [MemcpySource.store] using
    memmoveFromTraced_phase_order valuesPresent destination
      (.distinctBacking source) dst src count hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_safe
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  ∃ updated, (copyFromTraced? valuesPresent destination source dst src).result = some updated ∧ (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size := by
-- proof
  rcases copyFrom_eq_some_of_bounds destination source dst src hdst hsrc with
    ⟨updated, hcopy⟩
  have hresult :
    (copyFromTraced? valuesPresent destination source dst src).result =
      some updated := by
    change (copyFromTraced? valuesPresent destination source dst src).erase =
      some updated
    rwa [erase_copyFromTraced]
  exact ⟨updated, hresult,
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc,
    copyFrom_entries_size_of_eq_some destination source updated dst src hcopy⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyTraced_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src) :
-- imply
  ∃ updated, (copyTraced? valuesPresent slice dst src).result = some updated ∧ (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size := by
-- proof
  simpa [copyTraced?] using
    copyFromTraced_safe valuesPresent slice slice dst src hdst hsrc

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromIncrTraced_safe
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  ∃ result, (copyFromIncrTraced? valuesPresent destination source dst src).result = some result ∧ ((copyFromIncrTraced? valuesPresent destination source dst src).trace |>.allAccessesInBounds) ∧ result.slice.entries.size = destination.entries.size ∧ ValuesModeInvariant valuesPresent result.slice ∧ ValuesModeInvariant valuesPresent source ∧ CursorInRange result.slice result.dst ∧ CursorInRange source result.src := by
-- proof
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize⟩
  let result : CursorResult κ ν :=
    { slice := updated, dst := dst + 1, src := src + 1 }
  have hresult :
    (copyFromIncrTraced? valuesPresent destination source dst src).result =
      some result := by
    simp [copyFromIncrTraced?, TraceResult.map, hcopy, result]
  refine ⟨result, hresult, ?_, hsize, ?_, hsource, ?_, ?_⟩
  · simpa [copyFromIncrTraced?, TraceResult.map] using hbounds
  · exact copyFromIncrTraced_valuesModeInvariant valuesPresent destination
    source dst src result hdestination hsource hresult
  · change CursorInRange updated (dst + 1)
    exact hdst.increment_cursorInRange.of_size_eq hsize
  · change CursorInRange source (src + 1)
    exact hsrc.increment_cursorInRange

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromDecrTraced_safe
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src)
  (hdstPositive : 0 < dst)
  (hsrcPositive : 0 < src) :
-- imply
  ∃ result, (copyFromDecrTraced? valuesPresent destination source dst src).result = some result ∧ ((copyFromDecrTraced? valuesPresent destination source dst src).trace |>.allAccessesInBounds) ∧ result.slice.entries.size = destination.entries.size ∧ ValuesModeInvariant valuesPresent result.slice ∧ ValuesModeInvariant valuesPresent source ∧ CursorInRange result.slice result.dst ∧ CursorInRange source result.src := by
-- proof
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize⟩
  let result : CursorResult κ ν :=
    { slice := updated, dst := dst - 1, src := src - 1 }
  have hresult :
    (copyFromDecrTraced? valuesPresent destination source dst src).result =
      some result := by
    simp [copyFromDecrTraced?, TraceResult.map, hcopy, result]
  refine ⟨result, hresult, ?_, hsize, ?_, hsource, ?_, ?_⟩
  · simpa [copyFromDecrTraced?, TraceResult.map] using hbounds
  · exact copyFromDecrTraced_valuesModeInvariant valuesPresent destination
    source dst src result hdestination hsource hresult
  · change CursorInRange updated (dst - 1)
    exact (hdst.decrement_cursorInRange hdstPositive).of_size_eq hsize
  · change CursorInRange source (src - 1)
    exact hsrc.decrement_cursorInRange hsrcPositive

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyIncrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyIncrTraced_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src)
  (hinvariant : ValuesModeInvariant valuesPresent slice) :
-- imply
  ∃ result, (copyIncrTraced? valuesPresent slice dst src).result = some result ∧ (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧ result.slice.entries.size = slice.entries.size ∧ ValuesModeInvariant valuesPresent result.slice ∧ CursorInRange result.slice result.dst ∧ CursorInRange result.slice result.src := by
-- proof
  rcases copyFromIncrTraced_safe valuesPresent slice slice dst src
    hinvariant hinvariant hdst hsrc with
    ⟨result, hresult, hbounds, hsize, hmode, _, hdstCursor, hsrcCursor⟩
  exact ⟨result, hresult, hbounds, hsize, hmode, hdstCursor,
    hsrcCursor.of_size_eq hsize⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyDecrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyDecrTraced_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src)
  (hdstPositive : 0 < dst)
  (hsrcPositive : 0 < src)
  (hinvariant : ValuesModeInvariant valuesPresent slice) :
-- imply
  ∃ result, (copyDecrTraced? valuesPresent slice dst src).result = some result ∧ (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧ result.slice.entries.size = slice.entries.size ∧ ValuesModeInvariant valuesPresent result.slice ∧ CursorInRange result.slice result.dst ∧ CursorInRange result.slice result.src := by
-- proof
  rcases copyFromDecrTraced_safe valuesPresent slice slice dst src
    hinvariant hinvariant hdst hsrc hdstPositive hsrcPositive with
    ⟨result, hresult, hbounds, hsize, hmode, _, hdstCursor, hsrcCursor⟩
  exact ⟨result, hresult, hbounds, hsize, hmode, hdstCursor,
    hsrcCursor.of_size_eq hsize⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[advanceTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma advanceTraced_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {index amount : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hmovement : CursorMovementInRange slice index amount) :
-- imply
  (advanceTraced valuesPresent index amount).result = some (advance index amount) ∧ (advanceTraced valuesPresent index amount).trace = AccessTrace.empty ∧ (advanceTraced valuesPresent index amount).trace.allAccessesInBounds ∧ CursorInRange slice (advance index amount) ∧ ValuesModeInvariant valuesPresent slice := by
-- proof
  exact ⟨rfl, rfl, AccessTrace.allAccessesInBounds_empty,
    hmovement.result, hinvariant⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_mode_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_mode_safe
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source)
  (hdst : IndexInBounds destination dst)
  (hsrc : IndexInBounds source src) :
-- imply
  ∃ updated, (copyFromTraced? valuesPresent destination source dst src).result = some updated ∧ (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size ∧ ValuesModeInvariant valuesPresent updated := by
-- proof
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    copyFromTraced_valuesModeInvariant valuesPresent destination source updated
      dst src hdestination hsource hresult⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyTraced_mode_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyTraced_mode_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hdst : IndexInBounds slice dst)
  (hsrc : IndexInBounds slice src) :
-- imply
  ∃ updated, (copyTraced? valuesPresent slice dst src).result = some updated ∧ (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size ∧ ValuesModeInvariant valuesPresent updated := by
-- proof
  rcases copyTraced_safe valuesPresent slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    copyTraced_valuesModeInvariant valuesPresent slice updated dst src
      hinvariant hresult⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_mode_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_mode_safe
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {dst src : Int}
-- given
  (hadmissible : source.Admissible dst src count)
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  ∃ updated, (memcpyTraced? valuesPresent count destination source dst src).result = some updated ∧ (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧ updated.entries.size = destination.entries.size ∧ ValuesModeInvariant valuesPresent updated := by
-- proof
  rcases memcpyTraced_safe valuesPresent count destination source dst src
    hadmissible hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memcpyTraced_valuesModeInvariant valuesPresent count destination source
      updated dst src hdestination hsource hresult⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveTraced_mode_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveTraced_mode_safe
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hinvariant : ValuesModeInvariant valuesPresent slice)
  (hdst : RangeInBounds slice dst count)
  (hsrc : RangeInBounds slice src count) :
-- imply
  ∃ updated, (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧ (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧ updated.entries.size = slice.entries.size ∧ ValuesModeInvariant valuesPresent updated := by
-- proof
  rcases memmoveTraced_safe valuesPresent slice dst src count hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memmoveTraced_valuesModeInvariant valuesPresent slice updated dst src count
      hinvariant hresult⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_mode_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_mode_safe
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {dst src : Int}
  {count : Nat}
-- given
  (hdestination : ValuesModeInvariant valuesPresent destination)
  (hsource : ValuesModeInvariant valuesPresent source.store)
  (hdst : RangeInBounds destination dst count)
  (hsrc : RangeInBounds source.store src count) :
-- imply
  ∃ updated, (memmoveFromTraced? valuesPresent destination source dst src count).result = some updated ∧ ((memmoveFromTraced? valuesPresent destination source dst src count).trace |>.allAccessesInBounds) ∧ updated.entries.size = destination.entries.size ∧ ValuesModeInvariant valuesPresent updated ∧ ValuesModeInvariant valuesPresent source.store := by
-- proof
  rcases memmoveFromTraced_safe valuesPresent destination source dst src count
    hdst hsrc with ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memmoveFromTraced_valuesModeInvariant valuesPresent destination source
      updated dst src count hdestination hsource hresult,
    hsource⟩

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {destination source updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : (copyFromTraced? valuesPresent destination source dst src).result = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  apply copyFrom_entries_size_of_eq_some destination source updated dst src
  rwa [← erase_copyFromTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : (copyTraced? valuesPresent slice dst src).result = some updated) :
-- imply
  updated.entries.size = slice.entries.size := by
-- proof
  apply copy_entries_size_of_eq_some slice updated dst src
  rwa [← erase_copyTraced valuesPresent slice dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncrTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromIncrTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : (copyFromIncrTraced? valuesPresent destination source dst src).result = some result) :
-- imply
  result.slice.entries.size = destination.entries.size := by
-- proof
  apply copyFromIncr_entries_size_of_eq_some destination source dst src result
  rwa [← erase_copyFromIncrTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecrTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyFromDecrTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : (copyFromDecrTraced? valuesPresent destination source dst src).result = some result) :
-- imply
  result.slice.entries.size = destination.entries.size := by
-- proof
  apply copyFromDecr_entries_size_of_eq_some destination source dst src result
  rwa [← erase_copyFromDecrTraced valuesPresent destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyIncrTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyIncrTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : (copyIncrTraced? valuesPresent slice dst src).result = some result) :
-- imply
  result.slice.entries.size = slice.entries.size := by
-- proof
  exact copyFromIncrTraced_entries_size_of_eq_some valuesPresent slice slice
    dst src result h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyDecrTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma copyDecrTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : (copyDecrTraced? valuesPresent slice dst src).result = some result) :
-- imply
  result.slice.entries.size = slice.entries.size := by
-- proof
  exact copyFromDecrTraced_entries_size_of_eq_some valuesPresent slice slice
    dst src result h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memcpyTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : (memcpyTraced? valuesPresent count destination source dst src).result = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  apply memcpy_entries_size_of_eq_some count destination source updated dst src
  rwa [← erase_memcpyTraced valuesPresent count destination source dst src]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {slice updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (h : (memmoveTraced? valuesPresent slice dst src count).result = some updated) :
-- imply
  updated.entries.size = slice.entries.size := by
-- proof
  apply memmove_entries_size_of_eq_some slice updated dst src count
  rwa [← erase_memmoveTraced valuesPresent slice dst src count]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFromTraced_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma memmoveFromTraced_entries_size_of_eq_some
  {valuesPresent : Bool}
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (h : (memmoveFromTraced? valuesPresent destination source dst src count).result = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  apply memmoveFrom_entries_size_of_eq_some destination source updated dst src count
  rwa [← erase_memmoveFromTraced valuesPresent destination source dst src count]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[sortslice_primitives_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
lemma sortslice_primitives_safe
-- imply
  SortSlicePrimitiveSafety κ ν := by
-- proof
  refine
    { eraseCopyFrom := erase_copyFromTraced
      eraseCopy := erase_copyTraced
      eraseCopyFromIncr := erase_copyFromIncrTraced
      eraseCopyFromDecr := erase_copyFromDecrTraced
      eraseCopyIncr := erase_copyIncrTraced
      eraseCopyDecr := erase_copyDecrTraced
      eraseMemcpy := erase_memcpyTraced
      sameBackingMemcpyRejectsOverlap :=
        memcpyTraced_sameBacking_overlap_rejected
      eraseMemmoveFrom := erase_memmoveFromTraced
      eraseMemmove := erase_memmoveTraced
      eraseAdvance := erase_advanceTraced
      falseModeRejectsPayload := falseMode_somePayload_violates_invariant
      copyEventOrder := ?_
      copyFromIncrEventOrder := ?_
      copyFromDecrEventOrder := ?_
      memcpyPhaseOrder := ?_
      memmoveFromPhaseOrder := ?_
      memmovePhaseOrder := ?_
      copyFromSafety := ?_
      copySafety := ?_
      copyFromIncrSafety := copyFromIncrTraced_safe
      copyFromDecrSafety := copyFromDecrTraced_safe
      copyIncrSafety := ?_
      copyDecrSafety := ?_
      memcpySafety := ?_
      memmoveFromSafety := memmoveFromTraced_mode_safe
      memmoveSafety := ?_
      advanceSafety := advanceTraced_safe
      copyFromExtent := copyFromTraced_entries_size_of_eq_some
      copyExtent := copyTraced_entries_size_of_eq_some
      copyFromIncrExtent := copyFromIncrTraced_entries_size_of_eq_some
      copyFromDecrExtent := copyFromDecrTraced_entries_size_of_eq_some
      copyIncrExtent := copyIncrTraced_entries_size_of_eq_some
      copyDecrExtent := copyDecrTraced_entries_size_of_eq_some
      memcpyExtent := memcpyTraced_entries_size_of_eq_some
      memmoveFromExtent := memmoveFromTraced_entries_size_of_eq_some
      memmoveExtent := memmoveTraced_entries_size_of_eq_some }
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromIncrTraced_accesses valuesPresent destination source dst src
      hdst hsrc
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromDecrTraced_accesses valuesPresent destination source dst src
      hdst hsrc
  · intro valuesPresent count destination source dst src _ _ hadmissible hdst hsrc
    exact memcpyTraced_phase_order valuesPresent count destination source dst src
      hadmissible hdst hsrc
  · intro valuesPresent destination source dst src count _ _ hdst hsrc
    cases source with
    | sameBacking =>
      exact memmoveFromTraced_sameBacking_phase_order valuesPresent destination
        dst src count hdst hsrc
    | distinctBacking source =>
      exact memmoveFromTraced_distinctBacking_phase_order valuesPresent count
        destination source dst src hdst hsrc
  · intro valuesPresent slice dst src count _ hdst hsrc
    exact memmoveTraced_phase_order valuesPresent slice dst src count hdst hsrc
  · intro valuesPresent destination source dst src hdestination hsource hdst hsrc
    exact copyFromTraced_mode_safe valuesPresent destination source dst src
      hdestination hsource hdst hsrc
  · intro valuesPresent slice dst src hinvariant hdst hsrc
    exact copyTraced_mode_safe valuesPresent slice dst src hinvariant hdst hsrc
  · intro valuesPresent slice dst src hinvariant hdst hsrc
    exact copyIncrTraced_safe valuesPresent slice dst src hdst hsrc hinvariant
  · intro valuesPresent slice dst src hinvariant hdst hsrc hdstPositive
    hsrcPositive
    exact copyDecrTraced_safe valuesPresent slice dst src hdst hsrc hdstPositive
      hsrcPositive hinvariant
  · intro valuesPresent count destination source dst src hdestination hsource
    hadmissible hdst hsrc
    exact memcpyTraced_mode_safe valuesPresent count destination source dst src
      hadmissible hdestination hsource hdst hsrc
  · intro valuesPresent slice dst src count hinvariant hdst hsrc
    exact memmoveTraced_mode_safe valuesPresent slice dst src count hinvariant
      hdst hsrc

end CPythonListsort.SortSlice

/--
[memcpyTraced_sameBacking_overlap_rejected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
private lemma memcpyTraced_sameBacking_overlap_rejected_eq
  {valuesPresent : Bool}
  {count : Nat}
  {destination : SortSlice κ ν}
  {dst src : Int}
-- given
  (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
-- imply
  (memcpyTraced? valuesPresent count destination .sameBacking dst src).result = none ∧ (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace = AccessTrace.empty ∧ (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase = memcpy? count destination .sameBacking dst src := by
-- proof
  apply CPythonListsort.memcpyTraced_sameBacking_overlap_rejected valuesPresent count destination dst src hoverlap

/--
[CursorMovementInRange.result](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean)
-/
@[path]
private lemma result_eq
  {slice : SortSlice κ ν}
  {index amount : Int}
-- given
  (h : CursorMovementInRange slice index amount) :
-- imply
  CursorInRange slice (advance index amount) := by
-- proof
  apply CPythonListsort.CursorMovementInRange.result h


-- created on 2026-10-23
