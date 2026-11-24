module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalFineRowProfileGrade
    {T : EvenTorus} (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Nat × Nat :=
  (∑ j : Fin T.height, (profile j).1.val,
    2 * ∑ j : Fin T.height, (profile j).2.val)


def sixVertexHorizontalFineRowProfileRowZero
    {T : EvenTorus} (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexHorizontalRowZeroProfile T :=
  fun j => (profile j).2.val

end
end StatMech.FrontierD
