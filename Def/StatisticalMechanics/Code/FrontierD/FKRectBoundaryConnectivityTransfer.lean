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
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def finiteBoundaryConnectivityGraph {V B : Type*} (G : SimpleGraph V)
    (embed : B -> V) : SimpleGraph B where
  Adj u v := u ≠ v ∧ G.Reachable (embed u) (embed v)
  symm := by
    constructor
    rintro u v ⟨huv, hreach⟩
    exact ⟨huv.symm, hreach.symm⟩
  loopless := ⟨by simp⟩

end
end StatMech.FrontierD
