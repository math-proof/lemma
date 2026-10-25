/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part2
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

def lpReplicaSubprofileReflectEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m} ≃
      {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        a <= fun e => m (lpReplicaCurrentEdgeReflect G sites e)} where
  toFun a := ⟨fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e), by
    intro e
    exact a.2 (lpReplicaCurrentEdgeReflect G sites e)⟩
  invFun a := ⟨fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e), by
    intro e
    have h := a.2 (lpReplicaCurrentEdgeReflect G sites e)
    change a.1 (lpReplicaCurrentEdgeReflect G sites e) <=
      m (lpReplicaCurrentEdgeReflect G sites
        (lpReplicaCurrentEdgeReflect G sites e)) at h
    rw [lpReplicaCurrentEdgeReflect_involutive] at h
    exact h⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext e
    exact congrArg a.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)
  right_inv := by
    intro a
    apply Subtype.ext
    funext e
    exact congrArg a.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)


end
end StatMech.Ising
