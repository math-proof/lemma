/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation
open SimpleGraph


set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*}


variable [Finite V] [DecidableEq V]


instance jes_cycle_coe_isFinite {G : SimpleGraph V} {w : V} (c : G.Walk w w) :
    Finite ↑c.toSubgraph.verts :=
  jcs_verts_finite c


end Lattice
end StatMech
