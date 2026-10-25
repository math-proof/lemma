/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open MeasureTheory Function Set
open scoped NNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def boxFinset (d n : ℕ) : Finset (Site d) := (box_finite d n).toFinset

end Percolation
end StatMech
