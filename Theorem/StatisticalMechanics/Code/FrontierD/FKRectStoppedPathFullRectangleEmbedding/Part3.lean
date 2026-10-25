/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part3
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

theorem fkRectStoppedPathFullRectangleEmbedding_injective
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    Function.Injective
      (fkRectStoppedPathFullRectangleEmbedding
        R center scale cut lower upper hfit) := by
  intro x y hxy
  apply rlcConnectorFullRectangleBoxInclusion_injective scale
  apply fkRectLocalBoxEmbedding_injective
    R center (2 * scale) cut lower upper hfit
  apply Subtype.ext
  exact hxy


theorem fkRectStoppedPathFullRectangleEmbedding_adjMatch
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (fkRectTorusGraph R)
      (fkRectStoppedPathFullRectangleEmbedding
        R center scale cut lower upper hfit) := by
  let incl := rlcConnectorFullRectangleBoxInclusion scale
  let emb := fkRectLocalBoxEmbedding
    R center (2 * scale) cut lower upper hfit
  have hbox := fkRectLocalBoxEmbedding_adjMatch
    R center (2 * scale) cut lower upper hcut hlower hfit
  intro x y
  exact (rlcConnectorFullRectangleBoxInclusion_adjMatch scale x y).trans
    (by
      change (FK.boxGraph 2 (2 * scale)).Adj (incl x) (incl y) ↔
        (fkRectTorusGraph R).Adj (emb (incl x)).1 (emb (incl y)).1
      exact hbox (incl x) (incl y))


end
end StatMech.FrontierD
