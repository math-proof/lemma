/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal


namespace StatMech.Ising

open ConfigSpace FK Lattice Percolation

variable {d : ℕ}


noncomputable def gvMinusMeasure (S : Finset (Site d)) (beta h : ℝ) :
    Measure (ConfigSpace (Site d)) :=
  gvMeasure (minusField d) S beta h

end StatMech.Ising
