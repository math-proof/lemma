/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectHorizontalCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  Finset.univ.image fun bx : Bool × Fin R.width =>
    (bx.1, (bx.2, (⟨0, R.height_pos⟩ : Fin R.height)))


def fkRectVerticalCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  Finset.univ.image fun y : Fin R.height =>
    (false, ((⟨0, R.width_pos⟩ : Fin R.width), y))


def fkRectTorusCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  fkRectHorizontalCutEdges R ∪ fkRectVerticalCutEdges R

end
end StatMech.FrontierD
