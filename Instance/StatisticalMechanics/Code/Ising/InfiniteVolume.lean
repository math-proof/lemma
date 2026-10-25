/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


instance instDecidableMemBox (d n : ℕ) (x : Site d) :
    Decidable (x ∈ box d n) := by
  rw [mem_box]; infer_instance


instance instDecidableAdj (d : ℕ) (x y : Site d) :
    Decidable ((hypercubicLattice d).Adj x y) := by
  rw [hypercubicLattice_adj]; infer_instance


end Ising
end StatMech
