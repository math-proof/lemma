/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TildePc
open MeasureTheory
open scoped NNReal
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def phi (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) : ℝ :=
  (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1


end Percolation
end StatMech
