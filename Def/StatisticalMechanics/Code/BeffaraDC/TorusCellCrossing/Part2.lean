/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusEdgeOfCode (L : ℕ) [Fact (2 < L)] :
    TorusEdgeCode L → TorusAmbientEdge L
  | ((x, y), .horizontal) => torusHorizontalEdge L x y
  | ((x, y), .vertical) => torusVerticalEdge L x y

end StatMech.BeffaraDC
