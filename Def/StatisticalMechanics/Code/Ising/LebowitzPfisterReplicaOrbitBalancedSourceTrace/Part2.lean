/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaDecoratedSourceCanonicalHalfBranch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  (Σ X : Finset (LPReplicaCurrentVertex V),
      {_s : LPReplicaBalancedSelector G sites B X q //
        Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding}) ⊕
    (Σ X : Finset (LPReplicaCurrentVertex V),
      {_s : LPReplicaBalancedSelector G sites B X q //
        Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding})

set_option maxHeartbeats 800000 in


noncomputable def lpReplicaDecoratedSourceCanonicalHalfBranch
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaDecoratedSourceCanonicalHalfBranch G sites i j q := by
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
  let s := lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z
  have hmissing := lpReplicaDecoratedSourceCanonicalHalf_missingSource
    G sites hsite hij q z
  dsimp only [Si, Sj, T, X] at hmissing
  have hi : B ∆ Si = Sj ∆ T := by
    ext x
    simp only [B, Finset.mem_symmDiff]
    tauto
  have hj : B ∆ Sj = Si ∆ T := by
    ext x
    simp only [B, Finset.mem_symmDiff]
    tauto
  by_cases hleft : B ∆ Si = X ∆ X.map lpReplicaCurrentReflect.toEmbedding
  · exact Sum.inl ⟨X, s, hi.symm.trans hleft⟩
  · have hright := hmissing.resolve_left (by simpa only [B] using hleft)
    exact Sum.inr ⟨X, s, hj.symm.trans hright⟩


def LPReplicaDecoratedSourceCanonicalHalfTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaOffdiagDecoratedSource G sites i j q ×
    LPReplicaDecoratedSourceCanonicalHalfBranch G sites i j q

noncomputable def lpReplicaDecoratedSourceCanonicalHalfTraceMap
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaDecoratedSourceCanonicalHalfTrace G sites i j q :=
  fun z => ⟨z,
    lpReplicaDecoratedSourceCanonicalHalfBranch G sites hsite hij q z⟩

end
end StatMech.Ising
