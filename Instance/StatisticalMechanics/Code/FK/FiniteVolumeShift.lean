/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable instance fvs_instFintypeTransBoxVerts (d m : ℕ) (v : Site d) :
    Fintype (fvs_transBoxVerts d m v) :=
  Fintype.ofEquiv (boxVerts d m) (fvs_transEquiv d m v)

instance fvs_instDecidableEqTransBoxVerts (d m : ℕ) (v : Site d) :
    DecidableEq (fvs_transBoxVerts d m v) :=
  Subtype.instDecidableEq


end FK
end StatMech
