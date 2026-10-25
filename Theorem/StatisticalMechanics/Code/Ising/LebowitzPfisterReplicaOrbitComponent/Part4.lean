/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part3
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

theorem lpReplicaReflectSubprofile_le_partialReflectProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) <=
      lpReplicaPartialReflectProfile G sites m p := by
  intro e
  unfold lpReplicaPartialReflectProfile
  exact Nat.le_add_left _ _


theorem lpReplicaSymmetrizedProfile_partialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m) :
    lpReplicaSymmetrizedProfile G sites
        (lpReplicaPartialReflectProfile G sites m p) =
      lpReplicaSymmetrizedProfile G sites m := by
  funext e
  have he : p e <= m e := hp e
  have hr : p (lpReplicaCurrentEdgeReflect G sites e) <=
      m (lpReplicaCurrentEdgeReflect G sites e) :=
    hp (lpReplicaCurrentEdgeReflect G sites e)
  unfold lpReplicaSymmetrizedProfile lpReplicaPartialReflectProfile
  rw [lpReplicaCurrentEdgeReflect_involutive]
  omega


theorem lpReplicaPartialReflectProfile_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m) :
    lpReplicaPartialReflectProfile G sites
        (lpReplicaPartialReflectProfile G sites m p)
        (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) = m := by
  funext e
  have he : p e <= m e := hp e
  unfold lpReplicaPartialReflectProfile
  dsimp only
  rw [lpReplicaCurrentEdgeReflect_involutive]
  omega


theorem lpReplicaSymmetrizedProfile_partialReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaSymmetrizedProfile G sites
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) =
      lpReplicaSymmetrizedProfile G sites m :=
  lpReplicaSymmetrizedProfile_partialReflect G sites m _
    (profileFlux_le (lpReplicaCurrentGraph G sites) m P)


end
end StatMech.Ising
