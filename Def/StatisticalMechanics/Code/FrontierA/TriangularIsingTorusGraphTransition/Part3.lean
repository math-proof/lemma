module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

def triangularTorusDirectionReverse : Fin 6 → Fin 6 :=
  ![1, 0, 3, 2, 5, 4]

end StatMech.FrontierA
