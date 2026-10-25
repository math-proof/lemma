/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

noncomputable instance triangularTorusVerticalEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusVerticalEdge L edge) := Classical.dec _


end StatMech.FrontierA
