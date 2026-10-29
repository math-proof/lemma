/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part3
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem surfaceSet_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
    surfaceSet d n ω = surfaceSet d n ω' := by
  classical
  have hcoord : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y) :=
    coord_of_agree n h
  have hG := openSubgraphInduce_box_congr n hcoord
  unfold surfaceSet connBdry ConnectedWithin
  rw [hG]


theorem surfaceEvent_dependsOn (n : ℕ) (S : Finset (Site d)) :
    DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ)))
      ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff : ω ∈ surfaceEvent d n S ↔ ω' ∈ surfaceEvent d n S := by
    unfold surfaceEvent; simp only [Set.mem_setOf_eq, surfaceSet_congr n h]
  by_cases hω : ω ∈ surfaceEvent d n S
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]


theorem measurableSet_surfaceEvent (n : ℕ) (S : Finset (Site d)) :
    MeasurableSet (surfaceEvent d n S) := by
  rw [eq_cylinder_restrict_image _ _ (surfaceEvent_dependsOn n S)]
  exact MeasurableSet.cylinder _ (S := _) MeasurableSet.of_discrete


theorem sum_surfaceProb (p : NNReal) (hp : p ≤ 1) (n : ℕ) :
    ∑ S ∈ (boxFinset d n).powerset,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) = 1 := by
  classical
  have hcover : (⋃ S ∈ (boxFinset d n).powerset, surfaceEvent d n S) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨surfaceSet d n ω, Finset.mem_powerset.mpr (surfaceSet_subset_box n ω), rfl⟩
  have hdisj : ((boxFinset d n).powerset : Set (Finset (Site d))).PairwiseDisjoint
      (surfaceEvent d n) := by
    intro S _ S' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hωS hωS'
    exact hne (by rw [← (hωS : surfaceSet d n ω = S), ← (hωS' : surfaceSet d n ω = S')])
  have hmeas : ∀ S ∈ (boxFinset d n).powerset, MeasurableSet (surfaceEvent d n S) :=
    fun S _ => measurableSet_surfaceEvent n S
  rw [← measureReal_biUnion_finset hdisj hmeas, hcover]
  exact probReal_univ


end Percolation
end StatMech
