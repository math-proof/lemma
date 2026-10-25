import Mathlib
import sympy.Basic
import Theorem.CPythonListsort.Code.Transcription.SortSlice
open CPythonListsort CPythonListsort.SortSlice


namespace CPythonListsort.SortSlice

/--
[memcpy_sameBacking_overlap_rejected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memcpy_sameBacking_overlap_rejected
  {count : Nat}
  {destination : SortSlice κ ν}
  {dst src : Int}
-- given
  (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
-- imply
  memcpy? count destination .sameBacking dst src = none := by
-- proof
  simp [memcpy?, MemcpySource.Admissible, hoverlap]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFrom_sameBacking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memmoveFrom_sameBacking
  {destination : SortSlice κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  memmoveFrom? destination .sameBacking dst src count = destination.memmove? dst src count := by
-- proof
  rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFrom_distinctBacking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memmoveFrom_distinctBacking
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  memmoveFrom? destination (.distinctBacking source) dst src count = memcpyCore? count destination source dst src := by
-- proof
  rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma write_entries_size_of_eq_some
  {slice updated : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (h : slice.write? index entry = some updated) :
-- imply
  updated.entries.size = slice.entries.size := by
-- proof
  unfold write? at h
  split at h
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst updated
      simp
    · contradiction
  · contradiction

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFrom_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copyFrom_entries_size_of_eq_some
  {destination source updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : destination.copyFrom? source dst src = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  simp only [copyFrom?, bind, Option.bind] at h
  split at h
  · simp at h
  · exact write_entries_size_of_eq_some _ _ _ _ h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copy_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copy_entries_size_of_eq_some
  {slice updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : slice.copy? dst src = some updated) :
-- imply
  updated.entries.size = slice.entries.size :=
-- proof
  copyFrom_entries_size_of_eq_some _ _ _ _ _ h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromIncr_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copyFromIncr_entries_size_of_eq_some
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : destination.copyFromIncr? source dst src = some result) :
-- imply
  result.slice.entries.size = destination.entries.size := by
-- proof
  simp only [copyFromIncr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i updated hcopy
    have hresult :
      { slice := updated, dst := dst + 1, src := src + 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyFrom_entries_size_of_eq_some _ _ _ _ _ hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyFromDecr_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copyFromDecr_entries_size_of_eq_some
  {destination source : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : destination.copyFromDecr? source dst src = some result) :
-- imply
  result.slice.entries.size = destination.entries.size := by
-- proof
  simp only [copyFromDecr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i updated hcopy
    have hresult :
      { slice := updated, dst := dst - 1, src := src - 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyFrom_entries_size_of_eq_some _ _ _ _ _ hcopy

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyIncr_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copyIncr_entries_size_of_eq_some
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : slice.copyIncr? dst src = some result) :
-- imply
  result.slice.entries.size = slice.entries.size :=
-- proof
copyFromIncr_entries_size_of_eq_some slice slice dst src result h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copyDecr_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma copyDecr_entries_size_of_eq_some
  {slice : SortSlice κ ν}
  {dst src : Int}
  {result : CursorResult κ ν}
-- given
  (h : slice.copyDecr? dst src = some result) :
-- imply
  result.slice.entries.size = slice.entries.size :=
-- proof
copyFromDecr_entries_size_of_eq_some slice slice dst src result h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpyCore_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
private lemma memcpyCore_entries_size_of_eq_some (count : Nat)
  (destination source updated : SortSlice κ ν) (dst src : Int)
  (h : memcpyCore? count destination source dst src = some updated) :
  updated.entries.size = destination.entries.size := by
  induction count generalizing destination dst src with
  | zero =>
    simpa [memcpyCore?] using
      (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
    simp only [memcpyCore?, bind, Option.bind] at h
    split at h
    · simp at h
    · exact (ih _ _ _ h).trans (copyFrom_entries_size_of_eq_some _ _ _ _ _ ‹_›)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memcpy_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memcpy_entries_size_of_eq_some
  {count : Nat}
  {destination : SortSlice κ ν}
  {source : MemcpySource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
-- given
  (h : memcpy? count destination source dst src = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  unfold memcpy? at h
  split at h
  · exact memcpyCore_entries_size_of_eq_some _ _ _ _ _ _ h
  · simp at h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveForward_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
private lemma memmoveForward_entries_size_of_eq_some (count : Nat)
  (slice updated : SortSlice κ ν) (dst src : Int)
  (h : memmoveForward? count slice dst src = some updated) :
  updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
    simpa [memmoveForward?] using
      (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
    simp only [memmoveForward?, bind, Option.bind] at h
    split at h
    · simp at h
    · exact (ih _ _ _ h).trans (copy_entries_size_of_eq_some _ _ _ _ ‹_›)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveBackward_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
private lemma memmoveBackward_entries_size_of_eq_some (count : Nat)
  (slice updated : SortSlice κ ν) (dst src : Int)
  (h : memmoveBackward? count slice dst src = some updated) :
  updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
    simpa [memmoveBackward?] using
      (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
    simp only [memmoveBackward?, bind, Option.bind] at h
    split at h
    · simp at h
    · exact (ih _ _ _ h).trans (copy_entries_size_of_eq_some _ _ _ _ ‹_›)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmove_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memmove_entries_size_of_eq_some
  {slice updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (h : slice.memmove? dst src count = some updated) :
-- imply
  updated.entries.size = slice.entries.size := by
-- proof
  simp only [memmove?] at h
  split at h
  · exact memmoveForward_entries_size_of_eq_some _ _ _ _ _ h
  · exact memmoveBackward_entries_size_of_eq_some _ _ _ _ _ h

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmoveFrom_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean)
-/
@[path]
lemma memmoveFrom_entries_size_of_eq_some
  {destination : SortSlice κ ν}
  {source : MemmoveSource destination}
  {updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (h : memmoveFrom? destination source dst src count = some updated) :
-- imply
  updated.entries.size = destination.entries.size := by
-- proof
  cases source with
  | sameBacking =>
    exact memmove_entries_size_of_eq_some destination updated dst src count h
  | distinctBacking source =>
    exact memcpyCore_entries_size_of_eq_some count destination source updated
      dst src h

end CPythonListsort.SortSlice


-- created on 2026-10-23
