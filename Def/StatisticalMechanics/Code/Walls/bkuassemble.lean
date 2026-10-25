/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bktcuttransfer.Part2
import Theorem.StatisticalMechanics.Code.Walls.svccontraction
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


def bku_armPathCarrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type)) : Prop :=
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
    ∃ t₁ t₂ t₃ : (↑S : Type),
      bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
      ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
      G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃


end StatMech.Walls
