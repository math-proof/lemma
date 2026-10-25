/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Def.StatisticalMechanics.Code.FK.WiredDomChain.Part3
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem boxRestrictLE_boxRestrict (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (ω : ConfigSpace (Sym2 (Site d))) :
    boxRestrictLE d h (boxRestrict d m ω) = boxRestrict d n ω := by
  funext eb
  show ω (edgeIncl d m (innerEdgeLE d h eb)) = ω (edgeIncl d n eb)
  rw [edgeIncl_innerEdgeLE]

theorem boxRestrictLE_monotone (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Monotone (boxRestrictLE d h) :=
  fun a b hab eb => hab (innerEdgeLE d h eb)


end FK
end StatMech
