/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Instance.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part2
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


def finiteTriangleGraph : (t : ℕ) → SimpleGraph (TriangleVertex t)
  | 0 => ⊥
  | t + 1 => threeVertexTriangle ⊕g finiteTriangleGraph t

end StatMech.FrontierA
