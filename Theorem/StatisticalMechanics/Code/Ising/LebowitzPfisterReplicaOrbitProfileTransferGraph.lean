/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq
    (G : SimpleGraph V) (sites : I -> V)
    (m n q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q) :
    LPReplicaProfilePartialReflects G sites m n := by
  let p := fun e => m e - n e
  refine ⟨p, fun e => Nat.sub_le _ _, ?_⟩
  funext e
  have htot := congrFun (hm.trans hn.symm) e
  unfold lpReplicaSymmetrizedProfile at htot
  unfold lpReplicaPartialReflectProfile
  dsimp only [p]
  omega

theorem lpReplicaProfilePartialReflects_commonOrbit
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    LPReplicaProfilePartialReflects G sites m.1 n.1 :=
  lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq
    G sites m.1 n.1 q m.2 n.2


end
end StatMech.Ising
