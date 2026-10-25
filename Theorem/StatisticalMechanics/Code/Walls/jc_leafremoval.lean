/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.Walls.jc_leafremoval
open SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_pendant_existsUnique_induce (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
    ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u := by
  obtain ⟨u, ⟨huK, hadj⟩, huniq⟩ := h
  refine ⟨⟨u, huK⟩, ?_, ?_⟩
  · simp only [SimpleGraph.induce_adj]; exact hadj
  · rintro ⟨w, hwK⟩ hw
    simp only [SimpleGraph.induce_adj] at hw
    exact Subtype.ext (huniq w ⟨hwK, hw⟩)


theorem jc_pendant_nbr_finite (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u) :
    (((hypercubicLattice 2).induce K).neighborSet ⟨c, hc⟩).Finite := by
  obtain ⟨u, _, huniq⟩ := h
  apply Set.Finite.subset (Set.finite_singleton u)
  intro x hx
  rw [SimpleGraph.mem_neighborSet] at hx
  exact Set.mem_singleton_iff.mpr (huniq x hx)


theorem jc_cellConnected_diff_of_pendant (K : Set (Site 2)) (c : Site 2)
    (hconn : CellConnected K) (hpend : jc_IsPendantCell K c) :
    CellConnected (K \ {c}) := by
  obtain ⟨hc, hunique⟩ := hpend
  have hadj := jc_pendant_existsUnique_induce K c hc hunique
  letI : Fintype ↑(((hypercubicLattice 2).induce K).neighborSet ⟨c, hc⟩) :=
    (jc_pendant_nbr_finite K c hc hadj).fintype
  apply cellConnected_diff_of_degree_one K c hc hconn
  rw [degree_eq_one_iff_existsUnique_adj]
  exact hadj


theorem jc_leafRemoval (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (hconn : CellConnected K)
    (hunique : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
    CellConnected (K \ {c}) :=
  jc_cellConnected_diff_of_pendant K c hconn ⟨hc, hunique⟩


end Walls
end StatMech
