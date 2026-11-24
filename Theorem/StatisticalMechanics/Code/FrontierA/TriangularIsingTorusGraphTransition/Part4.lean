module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
public import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part3


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

@[simp] theorem triangularTorusDirectionStep_reverse
    (L : Nat) (a : Fin 6) :
    triangularTorusDirectionStep L (triangularTorusDirectionReverse a) =
      -triangularTorusDirectionStep L a := by
  fin_cases a <;>
    simp [triangularTorusDirectionReverse, triangularTorusDirectionStep]


end StatMech.FrontierA
