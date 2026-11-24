module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
public import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorus_localAngularSplit_det_eq_original
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L))
      (kwOrderedSplitWeight (triangularTorusGraph L) weight)
      (kwLocalAngularSplitPhase
        (triangularTorusLocalAngularData L rho hrho))).det =
      (1 - kwGraphTransition (triangularTorusGraph L) weight
        (triangularTorusGraphPhase L rho 1 1)).det := by
  exact kwLocalAngularSplit_det_eq_original
    (triangularTorusLocalAngularData L rho hrho) weight

end StatMech.FrontierA
