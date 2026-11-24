module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
public import Instance.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def anisotropicSquareEdgeWeight
    (L : Nat) (x y : Complex) : Sym2 (ZMod L × ZMod L) → Complex :=
  fun edge ↦ if squareTorusHorizontalEdge L edge then x else y

end StatMech.FrontierA
