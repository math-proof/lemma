/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfggenuinecarrier.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Theorem.StatisticalMechanics.Code.Walls.bgeexploration
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


def bge_ArmComponents (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ comp : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4 → Set (Site d),
    (∀ p : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, p.2 ≠ 0 →
      (comp p ∩ vertexBoundary d R).Nonempty) ∧
    (∀ p : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, p.2 ≠ 0 →
      ∀ q : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, q.2 ≠ 0 → p ≠ q →
      Disjoint (comp p) (comp q))

end StatMech.Walls
