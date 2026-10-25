/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def twoPeierlsBound (d : ℕ) (β : ℝ) : ℝ := 2 * peierlsBound d β


end Ising
end StatMech
