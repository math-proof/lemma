/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.FK.Uniqueness
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessFull.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace


section InfiniteVolume

open StatMech.Lattice


noncomputable def wiredEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (wiredInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0


noncomputable def freeEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (freeInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0


end InfiniteVolume
end FK
end StatMech
