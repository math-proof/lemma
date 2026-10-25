/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part6
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaReflectProfileEquiv
    (G : SimpleGraph V) (sites : I -> V) :
    ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ≃
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  toFun b := fun e => b (lpReplicaCurrentEdgeReflect G sites e)
  invFun b := fun e => b (lpReplicaCurrentEdgeReflect G sites e)
  left_inv := by
    intro b
    funext e
    dsimp only
    rw [lpReplicaCurrentEdgeReflect_involutive]
  right_inv := by
    intro b
    funext e
    dsimp only
    rw [lpReplicaCurrentEdgeReflect_involutive]


def lpReplicaPairEquivCollisionSigma
    (G : SimpleGraph V) (sites : I -> V) :
    (((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ×
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat)) ≃
      (Σ m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat,
        {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m}) :=
  (Equiv.prodCongr (Equiv.refl _)
    (lpReplicaReflectProfileEquiv G sites)).trans
      (StatMech.Sharpness.pairEquivSigma
        (E := (lpReplicaCurrentGraph G sites).edgeFinset))

end
end StatMech.Ising
