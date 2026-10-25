/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part7
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

def lpReplicaPartialReflectCopyEquivRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let p := profileFlux H m P
  let a := profileFlux H m (Finset.univ \ P)
  let split : Copy H m ≃ Copy H p ⊕ Copy H a :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr
        (lpReplicaCopySubsetEquivProfile G sites m P)
        ((lpReplicaCopyNotMemEquivCompl G sites m P).trans
          (lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P))))
  let collide : Copy H a ⊕ Copy H p ≃
      Copy H (lpReplicaCollisionProfile G sites a p) :=
    (Equiv.sumCongr (Equiv.refl _)
        (lpReplicaReflectCopyEquiv G sites p)).trans
      ((Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (p (lpReplicaCurrentEdgeReflect G sites e)))).symm.trans
        (lpReplicaCollisionCopyEquiv G sites a p))
  exact split |>.trans (Equiv.sumComm _ _) |>.trans collide


def lpReplicaPartialReflectCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) :=
  (lpReplicaPartialReflectCopyEquivRaw G sites m P).trans
    (Equiv.cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
      (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
        G sites m P)))

end
end StatMech.Ising
