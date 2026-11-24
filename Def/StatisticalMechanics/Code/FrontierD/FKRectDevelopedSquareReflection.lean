module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
public import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
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

def fkRectRowReflection (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) : Fin R.height :=
  ⟨(2 * center + R.height - y.val) % R.height,
    Nat.mod_lt _ R.height_pos⟩

end
end StatMech.FrontierD
