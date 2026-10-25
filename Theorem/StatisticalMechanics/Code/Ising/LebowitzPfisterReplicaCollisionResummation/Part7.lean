/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part8
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaPairEquivCollisionSigma_apply_fst
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaPairEquivCollisionSigma G sites (a, b)).1 =
      lpReplicaCollisionProfile G sites a b := rfl

@[simp] theorem lpReplicaPairEquivCollisionSigma_apply_subprofile
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaPairEquivCollisionSigma G sites (a, b)).2.1 = a := rfl

open StatMech.Sharpness


theorem lpReplicaWeight_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) =
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  apply Fintype.prod_equiv (lpReplicaCurrentEdgeReflect G sites)
  intro e
  simp only [lpReplicaCurrentEdgeReflect_val]
  rw [lpReplicaCurrentCoupling_reflect]

theorem lpReplicaReflectedResidual_weight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (lpReplicaReflectedResidual G sites m a)) =
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (fun e => m e - a e)) := by
  exact lpReplicaWeight_reflect G sites beta J hf r
    (fun e => m e - a e)


end
end StatMech.Ising
