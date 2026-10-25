/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfileOrbitMass_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  unfold lpReplicaProfileOrbitMass
  exact tsum_nonneg fun m => lpReplicaRowFiberMass_nonneg
    G sites beta J hf r hbeta hJ hhf hr A B m.1

theorem lpReplicaProfileOrbitMass_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaProfileOrbitMass G sites beta J hf r A B) := by
  have h := (lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B).hasSum.tsum_fiberwise
      (lpReplicaSymmetrizedProfile G sites)
  exact h.summable


theorem lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
      sourcePairDisconnSum H beta Jr B ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑' q, lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  dsimp only
  rw [lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
    G sites beta J hf r hbeta hJ hhf hr A B]
  have h := (lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B).hasSum.tsum_fiberwise
      (lpReplicaSymmetrizedProfile G sites)
  exact h.tsum_eq.symm


end
end StatMech.Ising
