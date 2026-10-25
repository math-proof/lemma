/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part3
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.neighbor_mem_buffered_succ
    (P : PeriodicGraph V) (n : ℕ) {v w : V}
    (hv : v ∈ P.orbitBox (P.bufferedRadius n))
    (hvw : P.graph.Adj v w) :
    w ∈ P.orbitBox (P.bufferedRadius (n + 1)) := by
  rw [P.bufferedRadius_succ]
  exact P.neighbor_mem_nextBufferedRadius (P.bufferedRadius n) hv hvw


theorem PeriodicGraph.not_bufferedBoundary_incl_succ
    (P : PeriodicGraph V) (n : ℕ) (v : P.BufferedVertex n) :
    ¬ P.bufferedBoundary (n + 1) (P.bufferedVertexIncl n v) := by
  rintro ⟨w, hvw, hw⟩
  exact hw (P.neighbor_mem_buffered_succ n v.2 hvw)

theorem PeriodicGraph.bufferedBoundary_of_outsideGraph_adj
    (P : PeriodicGraph V) (n : ℕ)
    (psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1))))
    {x : P.BufferedVertex n} {z : P.BufferedVertex (n + 1)}
    (h : (ocd_outsideGraph (P.bufferedGraph (n + 1))
      (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi).Adj
        (P.bufferedVertexIncl n x) z) :
    P.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hbdry, _⟩
  · have hznot : z.1 ∉ P.orbitBox (P.bufferedRadius n) := by
      intro hz
      let zIn : P.BufferedVertex n := ⟨z.1, hz⟩
      have hzEq : P.bufferedVertexIncl n zIn = z := Subtype.ext rfl
      apply hrange
      refine ⟨s(x, zIn), ?_⟩
      rw [ocd_innerEdge_mk, hzEq]
    exact ⟨z.1, hadj, hznot⟩
  · exact (P.not_bufferedBoundary_incl_succ n x hbdry).elim


theorem PeriodicGraph.bufferedInducedWiring_le (P : PeriodicGraph V) (n : ℕ)
    (psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1)))) :
    ocd_inducedWiring (P.bufferedGraph (n + 1))
        (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi
      ≤ StatMech.Lattice.boundaryCliqueGraph (P.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : P.bufferedVertexIncl n x ≠ P.bufferedVertexIncl n y :=
      fun h => hne ((P.bufferedVertexIncl n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact P.bufferedBoundary_of_outsideGraph_adj n psi hadj
  · have hreach' := hreach.symm
    have hne' : P.bufferedVertexIncl n y ≠ P.bufferedVertexIncl n x :=
      fun h => hne ((P.bufferedVertexIncl n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact P.bufferedBoundary_of_outsideGraph_adj n psi hadj


theorem PeriodicGraph.freeBuffered_step
    (P : PeriodicGraph V) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
    (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        fkProb (P.bufferedGraph n) p q omega) ≤
      ∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)) eta *
          fkProb (P.bufferedGraph (n + 1)) p q eta := by
  exact bdp_free_inner_dominated_fkProb
    (P.bufferedVertexIncl n).injective (P.bufferedAdjMatch n) hp hp1 hq hA


theorem PeriodicGraph.wiredBuffered_step
    (P : PeriodicGraph V) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
    (hA : IsIncreasing A) :
    (∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)) eta *
          wiredFkProb (P.bufferedGraph (n + 1))
            (P.bufferedBoundary (n + 1)) p q eta) ≤
      ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        wiredFkProb (P.bufferedGraph n) (P.bufferedBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (P.bufferedVertexIncl n).injective (P.bufferedAdjMatch n)
    (P.bufferedBoundary n) hp hp1 hq
    (fun psi => P.bufferedInducedWiring_le n psi) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h


end PeriodicPlanar
end FK
end StatMech
