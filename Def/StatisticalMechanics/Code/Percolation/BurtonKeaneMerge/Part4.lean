/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def HasFiniteEnergyMerge (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ F : Finset (Sym2 (Site d)), (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ


end Percolation
end StatMech
