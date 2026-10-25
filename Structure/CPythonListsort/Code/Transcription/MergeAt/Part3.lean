/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeAt.Part3
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Facts exported from the actual `merge_at` preparation path for a
subsequent `merge_getmem` call.  In particular, the guard-relevant state frame
is proved from the transcribed control flow, while the two trimming facts are
kept separately rather than replacing them with an assumed sum bound. -/
structure MergeAtCallsiteEvidence (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : Prop where
  leftSelected : pre.pending[i]? = some call.left
  rightSelected : pre.pending[i + 1]? = some call.right
  ssa_eq :
    call.ssa = Int.ofNat (call.left.base + call.trimA.index)
  ssb_eq : call.ssb = Int.ofNat call.right.base
  listlen_eq : call.state.listlen = pre.listlen
  basekeys_eq : call.state.basekeys = pre.basekeys
  data_eq : call.state.data = pre.data
  dataSize_eq : call.state.data.entries.size = pre.data.entries.size
  storage_eq : call.state.a = pre.a
  hasValues_eq : call.state.a.hasValues = pre.a.hasValues
  alloced_eq : call.state.alloced = pre.alloced
  pending_eq :
    call.state.pending =
      (pre.pending.setIfInBounds i
        { call.left with len := call.left.len + call.right.len }).eraseIdxIfInBounds
          (i + 1)
  firstBRead :
    call.state.data.read? (Int.ofNat call.right.base) = some call.firstB
  rightGallop :
    gallopRight? call.state call.state.data (Int.ofNat call.left.base)
      call.firstB.key call.left.len.toNat 0 = some call.trimA
  leftRemainder : call.na = call.left.len.toNat - call.trimA.index
  lastARead :
    call.state.data.read?
      (Int.ofNat (call.left.base + call.trimA.index + call.na - 1)) =
        some call.lastA
  leftGallop :
    gallopLeft? call.state call.state.data (Int.ofNat call.right.base)
      call.lastA.key call.right.len.toNat (call.right.len.toNat - 1) =
        some call.trimB
  rightRemainder : call.nb = call.trimB.index
  leftPositive : 0 < call.na
  rightPositive : 0 < call.nb

end CPythonListsort
