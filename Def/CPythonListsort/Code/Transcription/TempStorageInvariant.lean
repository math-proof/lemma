/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/TempStorageInvariant.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
/-!
# Temporary merge-storage representation invariant

CPython stores temporary keys and optional values in one raw pointer block.
The Lean model pairs one key with its optional value in each logical cell, so a
keyed logical cell represents two physical pointer slots while an unkeyed cell
represents one.  The invariant below connects that abstraction to `alloced` and
to the fixed inline buffer.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace TempStorage

/-- Number of raw pointer slots used per logical temporary entry. -/
def multiplier (storage : TempStorage κ ν) : Nat :=
  if storage.hasValues then 2 else 1

/-- Number of raw pointer slots represented by the logical cell array. -/
def physicalSlots (storage : TempStorage κ ν) : Nat :=
  storage.multiplier * storage.cells.size

/-- Payload cells are accessible exactly while backing storage is live. -/
def Live (storage : TempStorage κ ν) : Prop :=
  storage.backing ≠ .released

end TempStorage

/--
Reachability invariant for temporary merge storage. Inline storage must fit the
256 raw pointer slots in `temparray`; keyed entries consume two pointer slots.
Heap storage records the same one-or-two-slot multiplier used by
`merge_getmem`. In the released case, `cells` is empty but there is deliberately
no relationship to `alloced`: pinned `merge_freemem` clears `a.keys` while
leaving `alloced` stale. `hasValues` likewise remains available as mode
metadata.
-/
def TempStorageInv (storage : TempStorage κ ν) (alloced : PySSize) : Prop :=
  match storage.backing with
  | .inline =>
      storage.cells.size = alloced.toNat ∧
        storage.multiplier * alloced.toNat ≤ MERGESTATE_TEMP_SIZE
  | .heap =>
      storage.cells.size = alloced.toNat ∧
        storage.physicalSlots = storage.multiplier * alloced.toNat
  | .released => storage.cells.isEmpty

namespace TempStorageInv

variable {storage : TempStorage κ ν} {alloced : PySSize}

/-- A deliberately impossible inline keyed state used to pin the invariant. -/
def impossibleInlineKeyed255 : TempStorage Unit Unit :=
  { cells := Array.replicate 255 none
    backing := .inline
    hasValues := true }

end TempStorageInv
end CPythonListsort
