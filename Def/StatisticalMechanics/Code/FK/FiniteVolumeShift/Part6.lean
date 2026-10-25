/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Instance.StatisticalMechanics.Code.FK.FiniteVolumeShift
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


def fvs_transBoxGraph (d m : ℕ) (v : Site d) : SimpleGraph (fvs_transBoxVerts d m v) :=
  SimpleGraph.comap Subtype.val (hypercubicLattice d)

end FK
end StatMech
