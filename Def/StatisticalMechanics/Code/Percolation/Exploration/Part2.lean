/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.Exploration
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def W (p : NNReal) (hp : p ≤ 1) (ω : ConfigSpace E) : ℝ := ∏ e, w1 p hp (ω e)


noncomputable def wsum (p : NNReal) (hp : p ≤ 1) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω : ConfigSpace E, f ω * W p hp ω


end Finite
end Percolation
end StatMech
