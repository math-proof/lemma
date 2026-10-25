/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part4
open MeasureTheory
open scoped BigOperators


set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (edgeIncl d n) then ω h.choose else false


end FK
end StatMech
