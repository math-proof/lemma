/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part6
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarHexBufferedToFiniteStar_embedding_eq
    (n : Nat) (v : hexagonal.BufferedVertex n) :
    triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n)
        (triHexPlanarHexBufferedToFiniteStar n v) = v.1 :=
  by
    simpa [triHexPlanarHexBufferedOuterStarLevel,
      triHexPlanarHexBufferedToFiniteStar] using
      (Classical.choose_spec
        (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
          (hexagonal.bufferedRadius (n + 1))
          (hexagonal.orbitBox_mono
            (hexagonal.bufferedRadius_strictMono.monotone
              (Nat.le_succ n)) v.2)))

theorem triHexPlanarHexBufferedToFiniteStar_adjMatch (n : Nat) :
    ocd_AdjMatch (hexagonal.bufferedGraph n)
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel n))
      (triHexPlanarHexBufferedToFiniteStar n) := by
  intro x y
  rw [triHexPlanarFiniteStarGraph_adj_iff_hexagonal]
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq,
    triHexPlanarHexBufferedToFiniteStar_embedding_eq]
  rfl

theorem triHexPlanarHexBufferedToFiniteStar_not_boundary
    (n : Nat) (v : hexagonal.BufferedVertex n) :
    ¬ triHexPlanarFiniteStarBoundary
      (triHexPlanarHexBufferedOuterStarLevel n)
      (triHexPlanarHexBufferedToFiniteStar n v) := by
  rw [triHexPlanarFiniteStar_boundary_iff_ambient]
  rintro ⟨w, hadj, hw⟩
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq] at hadj
  apply hw
  apply hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
    (hexagonal.bufferedRadius (n + 1))
  exact hexagonal.neighbor_mem_buffered_succ n v.2 hadj

theorem triHexPlanarHexBuffered_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n))))
    (x : hexagonal.BufferedVertex n)
    {c : TriHexPlanarFiniteStarVertex
      (triHexPlanarHexBufferedOuterStarLevel n)}
    (h : (ocd_outsideGraph
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel n))
      (triHexPlanarHexBufferedToFiniteStar n)
      (triHexPlanarFiniteStarBoundary
        (triHexPlanarHexBufferedOuterStarLevel n)) psi).Adj
        (triHexPlanarHexBufferedToFiniteStar n x) c) :
    hexagonal.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · refine ⟨triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n) c, ?_, ?_⟩
    · rw [← triHexPlanarHexBufferedToFiniteStar_embedding_eq n x]
      exact triHexPlanarFiniteStarGraph_adj_hexagonal _ hadj
    · intro hc
      apply hnotRange
      let z : hexagonal.BufferedVertex n :=
        ⟨triHexPlanarFiniteStarVertexEmbedding
            (triHexPlanarHexBufferedOuterStarLevel n) c, hc⟩
      refine ⟨s(x, z), ?_⟩
      rw [ocd_innerEdge_mk]
      congr 1
      apply (triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n)).injective
      rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq]
  · exact (triHexPlanarHexBufferedToFiniteStar_not_boundary n x houter).elim

theorem triHexPlanarHexBuffered_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n)))) :
    ocd_inducedWiring
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel n))
        (triHexPlanarHexBufferedToFiniteStar n)
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel n)) psi ≤
      boundaryCliqueGraph (hexagonal.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarHexBufferedToFiniteStar n x ≠
        triHexPlanarHexBufferedToFiniteStar n y :=
      fun h => hne ((triHexPlanarHexBufferedToFiniteStar n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarHexBuffered_boundary_of_outsideGraph_adj n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarHexBufferedToFiniteStar n y ≠
        triHexPlanarHexBufferedToFiniteStar n x :=
      fun h => hne ((triHexPlanarHexBufferedToFiniteStar n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarHexBuffered_boundary_of_outsideGraph_adj n psi y hadj


theorem triHexPlanarHexBuffered_outerStar_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (hexagonal.BufferedVertex n)))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb
          (triHexPlanarFiniteStarGraph
            (triHexPlanarHexBufferedOuterStarLevel n))
          (triHexPlanarFiniteStarBoundary
            (triHexPlanarHexBufferedOuterStarLevel n)) p q rho) ≤
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (hexagonal.bufferedGraph n)
          (hexagonal.bufferedBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarHexBufferedToFiniteStar n).injective
    (triHexPlanarHexBufferedToFiniteStar_adjMatch n)
    (hexagonal.bufferedBoundary n) hp hp1 hq
    (triHexPlanarHexBuffered_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h


end
end StatMech.FK.PeriodicPlanar
