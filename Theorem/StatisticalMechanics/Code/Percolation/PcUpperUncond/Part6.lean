/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part5
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


theorem mapLe_length (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) :
    (c.mapLe (faceBoundaryGraph_le S)).length = c.length :=
  Walk.length_map (Hom.ofLE (faceBoundaryGraph_le S)) c


theorem mapLe_edges (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) :
    (c.mapLe (faceBoundaryGraph_le S)).edges = c.edges := by
  show (c.map (Hom.ofLE (faceBoundaryGraph_le S))).edges = c.edges
  rw [SimpleGraph.Walk.edges_map]; simp [SimpleGraph.Hom.ofLE]


theorem mapLe_dart_faceAdj (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) (D : (hypercubicLattice 2).Dart)
    (hD : D ∈ (c.mapLe (faceBoundaryGraph_le S)).darts) :
    (faceBoundaryGraph S).Adj D.fst D.snd := by
  have hedge : D.edge ∈ (c.mapLe (faceBoundaryGraph_le S)).edges := List.mem_map_of_mem hD
  rw [mapLe_edges S c] at hedge
  rw [show D.edge = s(D.fst, D.snd) from rfl] at hedge
  exact c.adj_of_mem_edges hedge


theorem sharedPrimalEdge_isClosed {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) {f g : Site 2}
    (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
    ω (sharedPrimalEdge f g) = false := by
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge h.1
  have hbd : bdEdge (cluster 2 ω o) (sharedPrimalEdge f g) := h.2
  rw [hpq, bdEdge_mk] at hbd
  have hpqbd : (p, q) ∈ edgeBoundary 2 (cluster 2 ω o) := ⟨hadj, hbd⟩
  rw [hpq]
  exact cluster_edgeBoundary_isClosed o hpqbd


theorem percolationEventCompl_subset (henc : PcAnchoredEnclosure) :
    (percolationEvent 2)ᶜ ⊆ ⋃ ℓ : ℕ, ⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2 := by
  classical
  intro ω hω
  
  rw [Set.mem_compl_iff, mem_percolationEvent, Set.not_infinite] at hω
  
  obtain ⟨u, c, hcyc, hu⟩ := henc ω hω
  
  set c' : (hypercubicLattice 2).Walk u u :=
    c.mapLe (faceBoundaryGraph_le (cluster 2 ω (origin 2))) with hc'
  have hc'cyc : c'.IsCycle :=
    Walk.IsCycle.mapLe (faceBoundaryGraph_le (cluster 2 ω (origin 2))) hcyc
  have hc'len : c'.length = c.length := mapLe_length (cluster 2 ω (origin 2)) c
  
  have hmem : ω ∈ closedCircuitEvent c' := by
    intro D hD
    have hadj : (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj D.fst D.snd :=
      mapLe_dart_faceAdj (cluster 2 ω (origin 2)) c D hD
    exact sharedPrimalEdge_isClosed (origin 2) hadj
  
  have hu' : u ∈ anchorFinset c'.length := by rw [hc'len]; exact hu
  
  refine Set.mem_iUnion.2 ⟨c'.length, ?_⟩
  refine Set.mem_iUnion.2 ⟨⟨u, c'⟩, ?_⟩
  refine Set.mem_iUnion.2 ⟨?_, hmem⟩
  unfold cyclesAtLen
  rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff]
  exact ⟨hu', rfl, hc'cyc⟩


theorem measure_compl_percolationEvent_le (henc : PcAnchoredEnclosure) (p : NNReal) (hp : p ≤ 1)
    (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) ((percolationEvent 2)ᶜ)
      ≤ ENNReal.ofReal (2 * pcUpperBound (p : ℝ)) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp with hμ
  calc μ ((percolationEvent 2)ᶜ)
      ≤ μ (⋃ ℓ : ℕ, ⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2) :=
        measure_mono (percolationEventCompl_subset henc)
    _ ≤ ∑' ℓ : ℕ, μ (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2) := measure_iUnion_le _
    _ ≤ ∑' ℓ : ℕ, ((2 * ℓ * 4 ^ ℓ : ℕ) : ENNReal) * ((1 - p : NNReal) : ENNReal) ^ ℓ :=
        ENNReal.tsum_le_tsum (fun ℓ => measure_cyclesAtLen_le p hp ℓ)
    _ = ∑' ℓ : ℕ, ENNReal.ofReal (pcSummandTwo (p : ℝ) ℓ) :=
        tsum_congr (fun ℓ => ennSummand_eq_ofReal p hp ℓ)
    _ = ENNReal.ofReal (∑' ℓ : ℕ, pcSummandTwo (p : ℝ) ℓ) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun ℓ => pcSummandTwo_nonneg (by exact_mod_cast hp) ℓ)
          (summable_pcSummandTwo (p : ℝ) hsum)).symm
    _ = ENNReal.ofReal (2 * pcUpperBound (p : ℝ)) := by rw [tsum_pcSummandTwo]


theorem one_sub_theta_le (henc : PcAnchoredEnclosure) (p : NNReal) (hp : p ≤ 1)
    (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
    1 - theta 2 p hp ≤ 2 * pcUpperBound (p : ℝ) := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp with hμ
  
  have hsuper : 1 - theta 2 p hp ≤ μ.real ((percolationEvent 2)ᶜ) := by
    have hsub : μ Set.univ ≤ μ (percolationEvent 2) + μ ((percolationEvent 2)ᶜ) := by
      have huniv : (Set.univ : Set (ConfigSpace (Sym2 (Site 2))))
          = percolationEvent 2 ∪ (percolationEvent 2)ᶜ := by simp
      rw [huniv]; exact measure_union_le _ _
    rw [measure_univ] at hsub
    have hA : μ (percolationEvent 2) ≠ ⊤ := measure_ne_top _ _
    have hAc : μ ((percolationEvent 2)ᶜ) ≠ ⊤ := measure_ne_top _ _
    have hr := (ENNReal.toReal_le_toReal (by simp)
      (by simp [hA, hAc] : μ (percolationEvent 2) + μ ((percolationEvent 2)ᶜ) ≠ ⊤)).mpr hsub
    rw [ENNReal.toReal_add hA hAc, ENNReal.toReal_one] at hr
    simp only [theta, Measure.real, hμ]
    linarith
  
  have hb : (0 : ℝ) ≤ 2 * pcUpperBound (p : ℝ) := by
    have := pcUpperBound_nonneg (p := (p : ℝ)) (by exact_mod_cast hp); linarith
  have hle : μ.real ((percolationEvent 2)ᶜ) ≤ 2 * pcUpperBound (p : ℝ) := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal hb (measure_compl_percolationEvent_le henc p hp hsum)
  linarith


theorem pc_lt_one_of_enclosure (henc : PcAnchoredEnclosure) : pc 2 < 1 := by
  
  have htail := pcUpperBound_tendsto_one
  have hhalf : ∀ᶠ p in nhds (1 : ℝ), pcUpperBound p < 1 / 2 :=
    htail.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  
  have hbase : ∀ᶠ p in nhds (1 : ℝ), ‖pcRatio p‖ < 1 := by
    have hlt := (pcRatio_tendsto_one).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    have hgt := (pcRatio_tendsto_one).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
    filter_upwards [hlt, hgt] with p hp hp'
    rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hhalf.and hbase)
  
  set p₀ : ℝ := max (1 - ε / 2) 0 with hp₀
  have hp₀lt : p₀ < 1 := by rw [hp₀]; exact max_lt (by linarith) (by norm_num)
  have hp₀0 : (0 : ℝ) ≤ p₀ := le_max_right _ _
  have hp₀ge : 1 - ε / 2 ≤ p₀ := le_max_left _ _
  
  have hkey : ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 / 2 ∧ ‖pcRatio p‖ < 1 := by
    intro p hlo hhi
    apply hball
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  
  set s : ℝ := (p₀ + 1) / 2 with hs
  have hp₀s : p₀ < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) ≤ s := by rw [hs]; linarith
  set sN : NNReal := s.toNNReal with hsN
  have hsNcoe : (sN : ℝ) = s := by rw [hsN]; exact Real.coe_toNNReal s hs0
  have hsN1 : sN ≤ 1 := by
    rw [hsN, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hslt.le
  have hsNlt1 : sN < 1 := by
    rw [hsN, ← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff_of_nonneg hs0]; exact hslt
  have hub : ∀ q ∈ subcriticalSet 2, q ≤ sN := by
    intro q hq
    by_contra hcon
    push Not at hcon
    have hqreal : s < (q : ℝ) := by
      have hsq : (sN : ℝ) < (q : ℝ) := by exact_mod_cast hcon
      rwa [hsNcoe] at hsq
    have hq1 : q ≤ 1 := hq.1
    have hp₀q : p₀ < (q : ℝ) := lt_trans hp₀s hqreal
    have hq1r : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    obtain ⟨hbnd, hbase'⟩ := hkey (q : ℝ) hp₀q hq1r
    
    have hcb : 1 - theta 2 q hq1 ≤ 2 * pcUpperBound (q : ℝ) := one_sub_theta_le henc q hq1 hbase'
    have hθ : 0 < theta 2 q hq1 := by nlinarith [hbnd]
    
    obtain ⟨hq', hzero⟩ := hq
    rw [show hq' = hq1 from rfl] at hzero
    exact (ne_of_gt hθ) hzero
  calc pc 2 = sSup (subcriticalSet 2) := rfl
    _ ≤ sN := csSup_le' hub
    _ < 1 := hsNlt1


end Percolation
end StatMech
