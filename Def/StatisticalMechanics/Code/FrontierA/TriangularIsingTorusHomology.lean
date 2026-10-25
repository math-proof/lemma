/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def triangularTorusSurfaceEdgeClass (L : Nat) :
    Sym2 (ZMod L × ZMod L) → SurfaceHomology 1 :=
  fun edge =>
    (fun _ => if triangularTorusXSeamEdge L edge then 1 else 0,
      fun _ => if triangularTorusYSeamEdge L edge then 1 else 0)

end StatMech.FrontierA
