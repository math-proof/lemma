module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectLiftedVertex (R : FKRectTorus) (p : Int × Int) : R.Vertex :=
  (fkRectIntModFin R.width_pos p.1,
    fkRectIntModFin R.height_pos p.2)

end
end StatMech.FrontierD
