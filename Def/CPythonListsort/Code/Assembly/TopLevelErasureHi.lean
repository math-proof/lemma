/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureHi.lean -/

import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
/-!
# Raw-domain erasure for `merge_hi`

These structural lemmas have no safety, layout, liveness, or comparator-law
premises.  They state only that deleting the genuine access trace recovers the
reviewed raw evaluator on its full modeled domain.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

def mergeHiTracedAllocatedTail? (state : MergeState κ ν)
    (ssa ssb : Int) (na nb : Nat) : TraceResult (MergeHiResult κ ν) :=
  (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit nb state 0 ssb).bind fun state =>
      let dest := ssb + Int.ofNat (nb - 1)
      let ssaCursor := ssa + Int.ofNat (na - 1)
      (mergeHiCopyDataDecrTraced? state dest ssaCursor).bind fun copied =>
        let cursor : MergeHiCursor κ ν :=
          { state := copied.state
            dest := copied.dst
            ssa := copied.src
            ssb := Int.ofNat (nb - 1)
            basea := ssa
            na := na - 1
            nb := nb
            minGallop := copied.state.min_gallop
            phase := .straight 0 0 }
        mergeHiLoopTraced? (na + nb) cursor

def mergeHiAllocatedTail? (state : MergeState κ ν)
    (ssa ssb : Int) (na nb : Nat) : Option (MergeHiResult κ ν) := do
  let state ← mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb state 0 ssb
  let dest := ssb + Int.ofNat (nb - 1)
  let ssaCursor := ssa + Int.ofNat (na - 1)
  let copied ← mergeHiCopyDataDecr? state dest ssaCursor
  let cursor : MergeHiCursor κ ν :=
    { state := copied.state
      dest := copied.dst
      ssa := copied.src
      ssb := Int.ofNat (nb - 1)
      basea := ssa
      na := na - 1
      nb := nb
      minGallop := copied.state.min_gallop
      phase := .straight 0 0 }
  mergeHiLoop? (na + nb) cursor

end CPythonListsort
