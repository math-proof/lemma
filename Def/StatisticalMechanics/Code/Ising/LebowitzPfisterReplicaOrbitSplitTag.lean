/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaOrbitCollisionSplitEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a
          (lpReplicaReflectedResidual G sites m a)) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e => b
      (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr
        ((lpReplicaCopySubsetEquivProfile G sites m P).trans
          (Equiv.cast (congrArg (Copy H) hP)))
        ((lpReplicaCopyNotMemEquivCompl G sites m P).trans
          ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
            (Equiv.cast (congrArg (Copy H)
              (lpReplicaCollisionSplit_complProfile G sites m a P hP))))))
  let collide : Copy H a ⊕ Copy H (fun e => b
      (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  exact split.trans collide


end
end StatMech.Ising
