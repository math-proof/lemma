/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


def triangularTorusTurnExponent : Fin 6 -> Fin 6 -> Int :=
  !![0, 0, 2, -2, 1, -3;
     0, 0, -2, 2, -3, 1;
     -2, 2, 0, 0, -1, 3;
     2, -2, 0, 0, 3, -1;
     -1, 3, 1, -3, 0, 0;
     3, -1, -3, 1, 0, 0]


def triangularTorusDirectionAngleClass : Fin 6 -> ZMod 8 :=
  ![4, 0, 6, 2, 5, 1]


end StatMech.FrontierA
