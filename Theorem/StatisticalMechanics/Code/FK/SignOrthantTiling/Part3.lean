/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.SignOrthantTiling.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem sot_negLogDoublingBound_of_crossSplit (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hsplit : ∀ j, sot_OrthantCrossSplit d t C j) :
    bxt_NegLogDoublingBound d t := by
  classical
  
  choose W _ _ H _ K _ hci hiso hH hIB hEdge using hsplit
  
  set I : ℕ → ℝ := fun j => ((fis_interface (boxGraph d (2 ^ j)) (H j) (K j)).card : ℝ) with hI
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · 
    intro j; exact Nat.cast_nonneg _
  · 
    exact sot_summable_of_surfaceBound d hd C hC I (fun j => Nat.cast_nonneg _) hIB
  · 
    intro j
    obtain ⟨φ⟩ := hiso j
    exact bxt_doublingBound_of_crossSplit t j (H j) (K j) (hci j) φ (hH j)
  · 
    intro j; exact hEdge j


theorem sot_boxGraph_zero_eq_bot (n : ℕ) : boxGraph 0 n = ⊥ := by
  ext a b
  simp only [boxGraph, SimpleGraph.comap_adj, SimpleGraph.bot_adj, hypercubicLattice_adj]
  constructor
  · intro h; rw [Finset.sum_fin_eq_sum_range] at h; simp at h
  · intro h; exact h.elim


end FK
end StatMech
