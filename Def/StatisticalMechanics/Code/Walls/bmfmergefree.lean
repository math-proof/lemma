/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bmf_a₁ : Site 2 := ![1, 0]

def bmf_a₂ : Site 2 := ![0, 1]

def bmf_a₃ : Site 2 := ![-1, 0]

def bmf_b₁ : Site 2 := ![2, 0]

def bmf_b₂ : Site 2 := ![0, 2]

def bmf_b₃ : Site 2 := ![-2, 0]


def bmf_I : Finset (Sym2 (Site 2)) :=
  {s(bmf_a₁, bmf_b₁), s(bmf_a₂, bmf_b₂), s(bmf_a₃, bmf_b₃)}


def bmf_η₀ : ConfigSpace ↥bmf_I := fun _ => true


def bmf_X : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω |
    ((cluster 2 (removeSite 0 ω) bmf_b₁).Infinite ∧
      (cluster 2 (removeSite 0 ω) bmf_b₂).Infinite ∧
      (cluster 2 (removeSite 0 ω) bmf_b₃).Infinite) ∧
    (¬ Connected 2 (removeSite 0 ω) bmf_b₁ bmf_b₂ ∧
      ¬ Connected 2 (removeSite 0 ω) bmf_b₁ bmf_b₃ ∧
      ¬ Connected 2 (removeSite 0 ω) bmf_b₂ bmf_b₃)}


end StatMech.Walls
