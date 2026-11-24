module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
public import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit.Part2
public import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
public import Theorem.StatisticalMechanics.Code.FK.IvProperties
public import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
public import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part2
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


noncomputable def boxRestrictLE (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (η : ConfigSpace (Sym2 (boxVerts d m))) : ConfigSpace (Sym2 (boxVerts d n)) :=
  fun eb => η (innerEdgeLE d h eb)


end FK
end StatMech
