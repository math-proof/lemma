/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RectangularBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3


namespace StatMech.FrontierA

def SeparatelySubadditive (F : Nat -> Nat -> Real) : Prop :=
  HorizontallySubadditive F /\ VerticallySubadditive F


def HasRectangularAreaBound (F : Nat -> Nat -> Real) : Prop :=
  exists L : Real, 0 <= L /\ forall m n : Nat,
    F m n <= L * (m : Real) * (n : Real)


end StatMech.FrontierA
