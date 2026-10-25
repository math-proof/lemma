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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part12
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryInitialState (W : Nat) : FKRectBoundaryState W where
  Adj u v := u.2 = v.2 ∧ u.1 ≠ v.1
  symm := by
    constructor
    rintro u v ⟨hcoord, hbool⟩
    exact ⟨hcoord.symm, hbool.symm⟩
  loopless := ⟨by simp⟩


def FKRectStripVertex (W : Nat) : Nat -> Type
  | 0 => Fin W
  | n + 1 => FKRectStripVertex W n ⊕ Fin W

noncomputable def fkRectStripVertexFintype (W : Nat) :
    (n : Nat) -> Fintype (FKRectStripVertex W n)
  | 0 => inferInstanceAs (Fintype (Fin W))
  | n + 1 => @instFintypeSum (FKRectStripVertex W n) (Fin W)
      (fkRectStripVertexFintype W n) inferInstance

end
end StatMech.FrontierD
