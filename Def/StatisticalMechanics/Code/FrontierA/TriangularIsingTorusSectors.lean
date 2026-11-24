module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
public import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def triangularTorusAdj (L : Nat)
    (u v : ZMod L × ZMod L) : Prop :=
  onsTorusAdj L u v ∨
    ((u.1 = v.1 + 1 ∧ u.2 = v.2 + 1) ∨
      (u.1 = v.1 - 1 ∧ u.2 = v.2 - 1))

end StatMech.FrontierA
