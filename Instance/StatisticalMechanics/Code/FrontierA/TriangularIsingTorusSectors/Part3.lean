/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable instance triangularTorusXSeamEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusXSeamEdge L edge) := Classical.dec _

noncomputable instance triangularTorusYSeamEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusYSeamEdge L edge) := Classical.dec _

end StatMech.FrontierA
