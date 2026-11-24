module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
public import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
public import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
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


instance (L : Nat) [Fact (2 < L)] :
    DecidableRel (triangularTorusGraph L).Adj :=
  inferInstanceAs (DecidableRel (triangularTorusAdj L))


end StatMech.FrontierA
