import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
open CPythonListsort CPythonListsort.TempStorageInv


namespace CPythonListsort.TempStorageInv

/--
[cells_size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/TempStorageInvariant.lean)
-/
@[path]
lemma cells_size_eq
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {alloced : PySSize}
-- given
  (hInv : TempStorageInv storage alloced)
  (hLive : storage.Live) :
-- imply
  storage.cells.size = alloced.toNat := by
-- proof
  cases hBacking : storage.backing with
  | inline =>
    have hInline : storage.cells.size = alloced.toNat ∧
      storage.multiplier * alloced.toNat ≤ MERGESTATE_TEMP_SIZE := by
      simpa only [TempStorageInv, hBacking] using hInv
    exact hInline.1
  | heap =>
    have hHeap : storage.cells.size = alloced.toNat ∧
      storage.physicalSlots = storage.multiplier * alloced.toNat := by
      simpa only [TempStorageInv, hBacking] using hInv
    exact hHeap.1
  | released =>
    rw [TempStorage.Live] at hLive
    exact (hLive hBacking).elim

end CPythonListsort.TempStorageInv

namespace CPythonListsort.TempStorageInv

/--
[keySlot_lt_physicalSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/TempStorageInvariant.lean)
-/
@[path]
lemma keySlot_lt_physicalSlots
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {alloced : PySSize}
  {i : Nat}
-- given
  (hInv : TempStorageInv storage alloced)
  (hLive : storage.Live)
  (hi : i < alloced.toNat) :
-- imply
  i < storage.physicalSlots := by
-- proof
  rw [TempStorage.physicalSlots, cells_size_eq hInv hLive]
  simp only [TempStorage.multiplier]
  split <;> omega

end CPythonListsort.TempStorageInv

namespace CPythonListsort.TempStorageInv

/--
[valueSlot_lt_physicalSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/TempStorageInvariant.lean)
-/
@[path]
lemma valueSlot_lt_physicalSlots
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {alloced : PySSize}
  {i : Nat}
-- given
  (hInv : TempStorageInv storage alloced)
  (hLive : storage.Live)
  (hValues : storage.hasValues = true)
  (hi : i < alloced.toNat) :
-- imply
  alloced.toNat + i < storage.physicalSlots := by
-- proof
  rw [TempStorage.physicalSlots, cells_size_eq hInv hLive]
  simp [TempStorage.multiplier, hValues]
  omega

end CPythonListsort.TempStorageInv

namespace CPythonListsort

/--
[impossibleInlineKeyed255_not_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/TempStorageInvariant.lean)
-/
@[path]
lemma impossibleInlineKeyed255_not_inv
  {κ : Type u}
  {ν : Type v} :
-- imply
  ¬ TempStorageInv impossibleInlineKeyed255 (255 : PySSize) := by
-- proof
  simp [TempStorageInv, impossibleInlineKeyed255, TempStorage.multiplier,
    MERGESTATE_TEMP_SIZE]

end CPythonListsort


-- created on 2026-10-23
