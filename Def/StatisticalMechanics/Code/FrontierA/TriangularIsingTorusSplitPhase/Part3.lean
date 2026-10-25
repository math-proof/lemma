/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase.Part2


namespace StatMech.FrontierA

open SimpleGraph


noncomputable def triangularTorusSplitPhaseGauge
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) : Complex :=
  if kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm then 1
  else
    triangularTorusSplitInternalGauge rho
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst))
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd))

end StatMech.FrontierA
