/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_offdiagFourFunctions_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (i j : I)
    (hfiber : LPReplicaOffdiagFiberInequality
      G sites beta J hf r i j) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Si ∆ Sj ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      sourcePairDisconnSum H beta Jr Si ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Sj ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 +
      sourcePairDisconnSum H beta Jr Sj ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Si ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  dsimp only
  apply lpReplica_disconn_fourFunctions_of_fiberwise
    G sites beta J hf r hbeta hJ hhf hr
  exact hfiber


theorem lpReplicaMatchingDisconn_le_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hfiber : ∀ i j : I, i ≠ j ->
      LPReplicaOffdiagFiberInequality G sites beta J hf r i j) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_offdiagFourFunctions
    G sites beta J hf r hbeta hJ hhf hr
  intro i j hij
  exact lpReplica_offdiagFourFunctions_of_fiberwise
    G sites beta J hf r hbeta hJ hhf hr i j (hfiber i j hij)

end
end StatMech.Ising
