/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part2


namespace StatMech.FrontierD

def fkRectBoolXorEquiv (b : Bool) : Bool ≃ Bool where
  toFun x := x ^^ b
  invFun x := x ^^ b
  left_inv x := by cases x <;> cases b <;> rfl
  right_inv x := by cases x <;> cases b <;> rfl


def fkRectClosedPairingAtEdge {R : FKRectTorus} (a : R.EdgeIndex) : Bool :=
  decide (Even a.2.2.val) ^^ a.1


def fkRectConfigurationToMedialPairing (R : FKRectTorus) :
    R.Configuration ≃ FKMedialLoopPairing R.medialTorus :=
  (Equiv.arrowCongr (fkRectTorusMedialEdgeEquiv R) (Equiv.refl Bool)).symm |>.trans
    (Equiv.piCongrRight fun v =>
      fkRectBoolXorEquiv
        (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)))

end StatMech.FrontierD
