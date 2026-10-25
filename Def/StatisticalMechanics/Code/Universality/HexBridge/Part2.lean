/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexBridge.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexContourEmb

variable {W I : Type*} (E : HexContourEmb W I)


def wtContour (i : I) : ℝ := E.wtSAW (E.emb i)


end HexContourEmb
end StatMech.Universality
