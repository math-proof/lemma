/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part3
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def infiniteClusters (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Set (Site d)) :=
  {C | C.Infinite ∧ ∃ x, C = cluster d ω x}


noncomputable def numInfiniteClusters (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : ℕ∞ :=
  (infiniteClusters d ω).encard


end Percolation
end StatMech
