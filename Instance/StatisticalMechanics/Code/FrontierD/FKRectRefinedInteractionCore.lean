module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

instance fkRectRefinedCoverSide_fact_eight (R : FKRectTorus) :
    Fact (8 < fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) :=
  ⟨fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R)⟩

end
end StatMech.FrontierD
