/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfile_le_symmetrizedProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    m <= lpReplicaSymmetrizedProfile G sites m := by
  intro e
  exact Nat.le_add_right (m e) _


theorem lpReplicaProfile_le_of_symmetrizedProfile_eq
    (G : SimpleGraph V) (sites : I -> V)
    {m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (hm : lpReplicaSymmetrizedProfile G sites m = q) :
    m <= q := by
  rw [<- hm]
  exact lpReplicaProfile_le_symmetrizedProfile G sites m


theorem lpReplicaSymmetrizedProfile_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaSymmetrizedProfile G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaSymmetrizedProfile G sites m := by
  funext e
  unfold lpReplicaSymmetrizedProfile
  dsimp only
  rw [lpReplicaCurrentEdgeReflect_involutive]
  exact Nat.add_comm _ _


end
end StatMech.Ising
