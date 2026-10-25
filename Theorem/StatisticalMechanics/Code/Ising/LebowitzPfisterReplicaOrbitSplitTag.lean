/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCollisionSplit_complProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
    profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P) =
      fun e => lpReplicaReflectedResidual G sites m a
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  rw [profileFlux_compl, hP]
  unfold lpReplicaReflectedResidual
  rw [lpReplicaCurrentEdgeReflect_involutive]

@[simp] theorem lpReplicaCopy_cast_edge
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (p q : H.edgeFinset -> Nat) (h : p = q)
    (c : Copy H p) :
    (cast (congrArg (Copy H) h) c).1 = c.1 := by
  subst q
  rfl

@[simp] theorem lpReplicaCopy_cast_index
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (p q : H.edgeFinset -> Nat) (h : p = q)
    (c : Copy H p) :
    (cast (congrArg (Copy H) h) c).2.val = c.2.val := by
  subst q
  rfl


end
end StatMech.Ising
