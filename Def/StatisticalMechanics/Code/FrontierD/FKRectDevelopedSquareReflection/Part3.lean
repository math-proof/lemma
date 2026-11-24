module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
public import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part2
open Set SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectionVertexEquiv (R : FKRectTorus) (center : Nat) :
    R.Vertex ≃ R.Vertex :=
  (Equiv.refl (Fin R.width)).prodCongr
    (fkRectRowReflectionEquiv R center)

end
end StatMech.FrontierD
