/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelectorGeneral
    (G : SimpleGraph V) (sites : I -> V)
    (B D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites B D q) :
    LPReplicaDecoratedOrbitAtom G sites (B ∆ D)
      (D.map lpReplicaCurrentReflect.toEmbedding) q := by
  let movedTag := lpReplicaToggleRows G sites s.profile s.selector s.tag
  have hgate0 := lpReplicaRowGate_toggle G sites s.profile B ∅
    s.tag s.selector s.gate s.trueSource s.row0Disconn s.row1Disconn
  dsimp only at hgate0
  rw [s.falseSource] at hgate0
  have hempty : (∅ : Finset (LPReplicaCurrentVertex V)) ∆ D = D := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hempty] at hgate0
  exact lpReplicaDecoratedOrbitAtomOfRowGate G sites s.profile q movedTag
    (B ∆ D) D s.orbit hgate0 s.orbitLabel


noncomputable def lpReplicaDecoratedSourceCanonicalHalfAtom
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B :=
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
    LPReplicaDecoratedOrbitAtom G sites (B ∆ X)
      (X.map lpReplicaCurrentReflect.toEmbedding) q := by
  dsimp only
  exact lpReplicaDecoratedOrbitAtomOfBalancedSelectorGeneral G sites _ _ q
    (lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z)

end
end StatMech.Ising
