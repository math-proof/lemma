/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

def triangularTorusVerticalEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ p : ZMod L × ZMod L, edge = s(p, (p.1, p.2 + 1))

end StatMech.FrontierA
