/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectLocalCriterion
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectInsertedFundamentalWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e) :=
  (p.mapLe (fkRectOpenGraph_le_insert R F e)).concat
    (fkRectOpenGraph_insert_adj_medialPrimals R F e)


end
end StatMech.FrontierD
