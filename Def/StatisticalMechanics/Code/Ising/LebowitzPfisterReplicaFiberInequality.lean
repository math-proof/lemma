/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaDisconnProfileTerm
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  exact (∑ S : Finset (Copy H m),
    (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
      (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
        then 1 else 0) *
      (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) *
      weight H beta Jr (ofEdgeFun H m)


noncomputable def lpReplicaDisconnProfileFamily
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (Finset (Copy (lpReplicaCurrentGraph G sites) m)) := by
  classical
  exact Finset.univ.filter fun S =>
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) S = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

end
end StatMech.Ising
