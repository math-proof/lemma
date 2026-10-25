/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem iInter_crossingEvent_eq_percolationEvent :
    (⋂ n : ℕ, crossingEvent d n) = percolationEvent d := by
  ext ω
  simp only [Set.mem_iInter, mem_crossingEvent, percolationEvent, Set.mem_setOf_eq,
    cluster_infinite_iff]
  constructor
  · 
    intro h m
    obtain ⟨v, hconn, hv⟩ := h (m + 1)
    exact ⟨v, by simpa using hv, hconn⟩
  · 
    intro h n
    obtain ⟨y, hyb, hyc⟩ := h (n - 1)
    exact ⟨y, hyc, hyb⟩


theorem measurableSet_crossingEvent (n : ℕ) :
    MeasurableSet (crossingEvent d n) := by
  have heq : crossingEvent d n
      = ⋃ y ∈ {y : Site d | y ∉ box d (n - 1)}, {ω | Connected d ω (origin d) y} := by
    ext ω
    simp only [mem_crossingEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun y _ => measurableSet_connected (origin d) y)


end FK
end StatMech
