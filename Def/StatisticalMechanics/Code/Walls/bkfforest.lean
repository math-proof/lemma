/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgfglobalforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkfforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bkf_CutTransfer (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type)) : Prop :=
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
    ∀ t t' : (↑S : Type),
      ¬ (bc67_contractedLattice ω L y).Reachable (t : Site d) (t' : Site d) →
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t t'


end StatMech.Walls
