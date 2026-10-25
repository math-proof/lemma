/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part9
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_false
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    ¬ LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
      G sites i j q hcard z := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  intro hrealize
  change ∃ cut : LPReplicaRightCoupledPairedCut
      G sites z.1.1.1 B d.1,
    lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 cut.selector =
      lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
    (let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
     D = Si ∨ D = Sj) at hrealize
  obtain ⟨cut, _, hD⟩ := hrealize
  rcases hD with hD | hD
  · exact cut.doubledHalf_ne_seamSource
      G sites z.1.1.1 B d.1 i hD
  · exact cut.doubledHalf_ne_seamSource
      G sites z.1.1.1 B d.1 j hD


end
end StatMech.Ising
