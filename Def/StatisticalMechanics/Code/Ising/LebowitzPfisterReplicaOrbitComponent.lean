/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part2
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

def lpReplicaProfileOrbitReflectEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        lpReplicaSymmetrizedProfile G sites m = q} ≃
      {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        lpReplicaSymmetrizedProfile G sites m = q} where
  toFun m := ⟨fun e => m.1 (lpReplicaCurrentEdgeReflect G sites e), by
    rw [lpReplicaSymmetrizedProfile_reflect, m.2]⟩
  invFun m := ⟨fun e => m.1 (lpReplicaCurrentEdgeReflect G sites e), by
    rw [lpReplicaSymmetrizedProfile_reflect, m.2]⟩
  left_inv := by
    intro m
    apply Subtype.ext
    funext e
    exact congrArg m.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)
  right_inv := by
    intro m
    apply Subtype.ext
    funext e
    exact congrArg m.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)


end
end StatMech.Ising
