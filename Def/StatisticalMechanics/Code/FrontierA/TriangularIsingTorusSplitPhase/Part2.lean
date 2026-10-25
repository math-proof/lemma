/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase


namespace StatMech.FrontierA

open SimpleGraph


def triangularTorusSplitIncreasingGaugeExponent : Fin 6 -> Nat :=
  ![0, 2, 1, 5, 0, 4]


def triangularTorusSplitDecreasingGaugeExponent : Fin 6 -> Nat :=
  ![1, 13, 12, 0, 0, 14]


noncomputable def triangularTorusSplitInternalGauge
    (rho : Complex) (a b : Fin 6) : Complex :=
  if (triangularTorusDirectionRank a).val <
      (triangularTorusDirectionRank b).val then
    rho ^ triangularTorusSplitIncreasingGaugeExponent a
  else
    rho ^ triangularTorusSplitDecreasingGaugeExponent a

end StatMech.FrontierA
