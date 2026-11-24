module
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part2
open scoped BigOperators
open Finset Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


def TriangleVertex : ℕ → Type
  | 0 => Empty
  | t + 1 => Fin 3 ⊕ TriangleVertex t

end StatMech.FrontierA
