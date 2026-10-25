/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem finiteBoundaryConnectivityGraph_reachable_iff
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) (u v : B) :
    (finiteBoundaryConnectivityGraph G embed).Reachable u v ↔
      G.Reachable (embed u) (embed v) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj p ih => exact hadj.2.trans ih
  · intro hreach
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · exact (show (finiteBoundaryConnectivityGraph G embed).Adj u v from
        ⟨huv, hreach⟩).reachable


end
end StatMech.FrontierD
