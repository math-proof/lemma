module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part6
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPrimalDualCrossingRepresentativeSourceIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    Finset (Fin (2 * R.height)) := by
  classical
  exact Finset.univ.image
    (fkRectPrimalDualCrossingRepresentativeSourceIndex R eta)

end
end StatMech.FrontierD
