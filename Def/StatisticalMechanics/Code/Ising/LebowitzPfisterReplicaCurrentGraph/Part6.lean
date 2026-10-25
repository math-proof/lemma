/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part5
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrent_reflectedMatchingCut
    (G : SimpleGraph V) (J : Sym2 V -> Real) (hf : V -> Real)
    (sites : I -> V) (r : Real) :
    LPReflectedMatchingCut
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCurrentCoupling J hf r)
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 where
  reflect := lpReplicaCurrentReflect
  involutive := lpReplicaCurrentReflect_involutive
  reflect_left := fun _ => rfl
  reflect_right := fun _ => rfl
  reflect_g0 := rfl
  reflect_g1 := rfl
  adj_iff := lpReplicaCurrentGraph_adj_reflect G sites
  coupling := lpReplicaCurrentCoupling_reflect J hf r

end
end StatMech.Ising
