/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEuler
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

theorem card_boundaryCliqueGraph_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry]
    (v0 : V) (hv0 : bdry v0) :
    Nat.card (boundaryCliqueGraph bdry).ConnectedComponent =
      Fintype.card {x : V // ¬ bdry x} + 1 := by
  rw [← Nat.card_congr (boundaryCliqueComponentEquiv bdry v0 hv0)]
  simp

end
end StatMech.Universality
