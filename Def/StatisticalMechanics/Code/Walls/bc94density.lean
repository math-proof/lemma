/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc93badbox
import Theorem.StatisticalMechanics.Code.Walls.bc90boxopenforest
import Theorem.StatisticalMechanics.Code.Walls.bc89genuinetrifae
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc94_GenuineTrifExistence (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < μ {ω | numInfiniteClusters d ω = ⊤} →
    0 < μ {ω | bc89_GenuineTrif d ω 0}


end StatMech.Walls
