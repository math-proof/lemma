/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem hrHD_threeMeetBox_subset_iUnion_routePre {n : ℕ} (hrt : hrHD_DisjointRouting d n) :
    threeMeetBox d n ⊆ ⋃ p : hrHD_RouteIdx d, hrHD_routePre p := by
  intro ω hω
  obtain ⟨G, a₁, a₂, a₃, hpre⟩ := hrt ω hω
  exact Set.mem_iUnion.mpr ⟨(G, a₁, a₂, a₃), hpre⟩


theorem hrHD_route_step
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (n : ℕ) (hrt : hrHD_DisjointRouting d n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ p : hrHD_RouteIdx d, μ (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2) = 0 := by
    intro p; exact le_antisymm (hcon p.2.1 p.2.2.1 p.2.2.2) bot_le
  have hpre0 : ∀ p : hrHD_RouteIdx d, μ (hrHD_routePre p) = 0 := by
    intro p
    have hpush : (μ.map (fun ω => forceOpenFinset p.1 ω))
          (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)
        = μ ((fun ω => forceOpenFinset p.1 ω) ⁻¹'
            (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)) :=
      Measure.map_apply (measurable_forceOpenFinset p.1)
        (hrHD_measurableSet_neighborTrifPrecursor _ _ _)
    have hnull : μ ((fun ω => forceOpenFinset p.1 ω) ⁻¹'
        (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)) = 0 := by
      rw [← hpush]; exact (hfe p.1) (hzero p)
    exact hnull
  have hsum : (∑' p : hrHD_RouteIdx d, μ (hrHD_routePre p)) = 0 := by
    simp only [hpre0, tsum_zero]
  have hunion0 : μ (⋃ p : hrHD_RouteIdx d, hrHD_routePre p) = 0 := by
    refine le_antisymm ?_ bot_le
    exact le_trans (measure_iUnion_le (μ := μ) (fun p => hrHD_routePre p)) (le_of_eq hsum)
  have hle : μ (threeMeetBox d n) ≤ μ (⋃ p : hrHD_RouteIdx d, hrHD_routePre p) :=
    measure_mono (hrHD_threeMeetBox_subset_iUnion_routePre hrt)
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)


theorem hrHD_route_of_routing
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  intro n hpos
  exact hrHD_route_step μ hfe n (hrt n) hpos


lemma hrHD_exists_three_independent_axes (hd : 3 ≤ d) :
    ∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;>
    · intro h; simp [Fin.ext_iff] at h


theorem hrHD_axis_corridor_branches
    (ω : ConfigSpace (Sym2 (Site d))) {j₁ j₂ j₃ : Fin d}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (L : ℕ) (hL : 1 ≤ L) :
    
    (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧ hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧ hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧
    ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
    
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) ∧
    
    (Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω))
        (hrHD_rayPt j₁ 1) (hrHD_rayPt j₁ (L : ℤ)) ∧
      Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω))
        (hrHD_rayPt j₂ 1) (hrHD_rayPt j₂ (L : ℤ)) ∧
      Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω))
        (hrHD_rayPt j₃ 1) (hrHD_rayPt j₃ (L : ℤ))) := by
  refine ⟨⟨hrHD_rayPt_one_ne_of_ne h12, hrHD_rayPt_one_ne_of_ne h13, hrHD_rayPt_one_ne_of_ne h23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    ?_, ?_, ?_, ?_⟩
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h12 hs
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h13 hs
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h23 hs
  · exact ⟨hrHD_corridor_connected_one_to_L ω j₁ L hL,
      hrHD_corridor_connected_one_to_L ω j₂ L hL,
      hrHD_corridor_connected_one_to_L ω j₃ L hL⟩


theorem hrHD_burton_keane_uniqueness_dim_ge_three
    (hd : 3 ≤ d)
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  ⟨hrHD_exists_three_independent_axes hd,
    burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
      (hrHD_route_of_routing μ hfe hrt)⟩

end Percolation
end StatMech
