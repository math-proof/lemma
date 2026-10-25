/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.FK.CriticalPoint.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


noncomputable def fkPc (d : ℕ) (q : ℝ) : ℝ :=
  sSup (fkSubcriticalSet d q)

end FK
end StatMech
