/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


noncomputable def fkTheta (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : ℝ :=
  ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)


end FK
end StatMech
