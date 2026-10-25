/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.RSW.CrossingDuality
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace RSW

namespace CrossingDuality

@[simp] theorem rcd_mem_dualBox {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ rcd_dualBox a b c d ↔ DualVerticalCrossing ω (a + 1) (b - 1) c d := Iff.rfl


end CrossingDuality
end RSW
end StatMech
