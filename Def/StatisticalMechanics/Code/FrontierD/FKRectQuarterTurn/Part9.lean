/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part8
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnSet (R : FKRectTorus) (hheight : 4 < R.height)
    (S : Set R.Vertex) :
    Set (fkRectQuarterTurnTorus R hheight).Vertex :=
  fkRectQuarterTurnVertexEquiv R hheight '' S


def fkRectQuarterTurnSetEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) (S : Set R.Vertex) :
    S ≃ fkRectQuarterTurnSet R hheight S where
  toFun v := ⟨fkRectQuarterTurnVertexEquiv R hheight v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectQuarterTurnVertexEquiv R hheight).symm v.1, by
    rcases v.2 with ⟨w, hw, hturn⟩
    rw [← hturn]
    rw [Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectQuarterTurnVertexEquiv R hheight).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectQuarterTurnVertexEquiv R hheight).apply_symm_apply v.1


def fkRectOpenGraphQuarterTurnInduceIso
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega)).induce
          (fkRectQuarterTurnSet R hheight S) where
  toEquiv := fkRectQuarterTurnSetEquiv R hheight S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_quarterTurn_adj R hheight omega x.1 y.1


end
end StatMech.FrontierD
