/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


noncomputable def dfi_openEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ E, (if ω e then (1:ℝ) else 0)


end FK
end StatMech
