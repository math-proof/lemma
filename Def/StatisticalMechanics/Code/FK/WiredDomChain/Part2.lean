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
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


def boxVertInclLE (d : ℕ) {n m : ℕ} (h : n ≤ m) (x : boxVerts d n) : boxVerts d m :=
  ⟨(x : Site d), box_mono d h x.2⟩


def innerEdgeLE (d : ℕ) {n m : ℕ} (h : n ≤ m) : Sym2 (boxVerts d n) → Sym2 (boxVerts d m) :=
  Sym2.map (boxVertInclLE d h)


end FK
end StatMech
