/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.TempStorageInvariant

/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/

namespace CPythonListsort

/-! ## Same-store merge movement provenance -/

/-- The four block-movement sites whose source and destination are both in
`MergeState.data`.  They are deliberately separate from the six tagged
temp/main `memcpy` sites: these calls require overlap-safe `memmove` semantics. -/
inductive MergeMemmoveCallsite where
  | loGallopB
  | loCopyBTail
  | hiGallopA
  | hiCopyATail
  deriving DecidableEq, Repr

/-- Site-tagged same-store movement.  The tag carries review provenance only;
the evaluator is definitionally the existing overlap-safe primitive. -/
def mergeDataMemmove? (_site : MergeMemmoveCallsite)
    (data : SortSlice κ ν) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  data.memmove? dst src count

/-- Transcription of `merge_freemem`. Inline storage is retained. Any
non-inline key storage is released and its allocated cells cease to be
accessible; `alloced` and `hasValues` are intentionally unchanged. -/
def mergeFreemem (state : MergeState κ ν) : MergeState κ ν :=
  if state.a.backing = .inline then
    state
  else
    { state with
      a := { state.a with cells := #[], backing := .released } }

/-! ## `merge_getmem` -/

/-- Observable control-flow outcome of `merge_getmem`. The `.grown` case is the
version-one successful-allocation abstraction. `.guardRejected` is not an
allocator failure: it is the deterministic `size_t` overflow guard from the C
source, which runs after `merge_freemem`. -/
inductive MergeGetmemOutcome where
  | reused
  | grown
  | guardRejected
  deriving DecidableEq, Repr

/-- C integer returned on each modeled path. Both successful paths return zero;
the deterministic allocation-size rejection returns minus one. -/
def MergeGetmemOutcome.returnCode : MergeGetmemOutcome → Int
  | .reused | .grown => 0
  | .guardRejected => -1

/-- State and return-path information produced by `merge_getmem`. -/
structure MergeGetmemResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  outcome : MergeGetmemOutcome

/-- Largest logical request whose one-or-two-slot heap allocation fits the
selected 64-bit `Py_ssize_t` allocation bound. -/
def mergeGetmemAllocationLimit (storage : TempStorage κ ν) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / storage.multiplier

/-- Transcription of `merge_getmem` under the version-one convention that a
guard-admitted `PyMem_Malloc` call succeeds. The reuse test is signed, as in C.
The allocation guard views `need` through the same-width unsigned `size_t`
cast, represented by `need.toNat`. Fresh heap cells are uninitialized and old
payload contents are deliberately discarded rather than copied. -/
def mergeGetmem (state : MergeState κ ν) (need : PySSize) :
    MergeGetmemResult κ ν :=
  if need.sle state.alloced then
    { state := state, outcome := .reused }
  else
    let allocationLimit := mergeGetmemAllocationLimit state.a
    let freed := mergeFreemem state
    if allocationLimit < need.toNat then
      { state := freed, outcome := .guardRejected }
    else
      { state :=
          { freed with
            a :=
              { cells := Array.replicate need.toNat none
                backing := .heap
                hasValues := freed.a.hasValues }
            alloced := need }
        outcome := .grown }
