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
open SimpleGraph


set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*}


noncomputable def jes_boundedRegionCount [Finite V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  nullity G


end Lattice
end StatMech
