/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Theorem.StatisticalMechanics.Code.Walls.bmfmergefree
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bmf_R₁ : Set (Site 2) := {x | x 1 = 0 ∧ 2 ≤ x 0}

def bmf_R₂ : Set (Site 2) := {x | x 0 = 0 ∧ 2 ≤ x 1}

def bmf_R₃ : Set (Site 2) := {x | x 1 = 0 ∧ x 0 ≤ -2}


def bmf_OnRay (e : Sym2 (Site 2)) : Prop :=
  ∃ x y : Site 2, e = s(x, y) ∧
    ((x ∈ bmf_R₁ ∧ y ∈ bmf_R₁) ∨ (x ∈ bmf_R₂ ∧ y ∈ bmf_R₂) ∨ (x ∈ bmf_R₃ ∧ y ∈ bmf_R₃))

open Classical in

noncomputable def bmf_omegaTri : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if bmf_OnRay e then true else false

end StatMech.Walls
