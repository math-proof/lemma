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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part5
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteStarToHexBuffered_adjMatch (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteStarGraph n)
      (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n) := by
  intro x y
  exact triHexPlanarFiniteStarGraph_adj_iff_hexagonal n x y

theorem triHexPlanarFiniteStarToHexBuffered_not_boundary
    (n : Nat) (v : TriHexPlanarFiniteStarVertex n) :
    ¬ hexagonal.bufferedBoundary (n + 2)
      (triHexPlanarFiniteStarToHexBuffered n v) := by
  let vPrev : hexagonal.BufferedVertex (n + 1) :=
    ⟨triHexPlanarFiniteStarVertexEmbedding n v, by
      apply hexagonal.orbitBox_mono (hexagonal.id_le_bufferedRadius (n + 1))
      exact triHexPlanarFiniteStar_range_subset_orbitBox_succ n ⟨v, rfl⟩⟩
  have hnot := hexagonal.not_bufferedBoundary_incl_succ (n + 1) vPrev
  simpa [triHexPlanarFiniteStarToHexBuffered, vPrev, Nat.add_assoc] using hnot

theorem triHexPlanarFiniteStar_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (hexagonal.BufferedVertex (n + 2))))
    (x : TriHexPlanarFiniteStarVertex n)
    {c : hexagonal.BufferedVertex (n + 2)}
    (h : (ocd_outsideGraph (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n)
      (hexagonal.bufferedBoundary (n + 2)) psi).Adj
        (triHexPlanarFiniteStarToHexBuffered n x) c) :
    triHexPlanarFiniteStarBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · apply (triHexPlanarFiniteStar_boundary_iff_ambient n x).2
    refine ⟨c.1, hadj, ?_⟩
    rintro ⟨z, hz⟩
    apply hnotRange
    refine ⟨s(x, z), ?_⟩
    rw [ocd_innerEdge_mk]
    congr 1
    exact Subtype.ext hz
  · exact (triHexPlanarFiniteStarToHexBuffered_not_boundary n x houter).elim

theorem triHexPlanarFiniteStar_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (hexagonal.BufferedVertex (n + 2)))) :
    ocd_inducedWiring (hexagonal.bufferedGraph (n + 2))
        (triHexPlanarFiniteStarToHexBuffered n)
        (hexagonal.bufferedBoundary (n + 2)) psi ≤
      boundaryCliqueGraph (triHexPlanarFiniteStarBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarFiniteStarToHexBuffered n x ≠
        triHexPlanarFiniteStarToHexBuffered n y :=
      fun h => hne ((triHexPlanarFiniteStarToHexBuffered n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarFiniteStar_boundary_of_outsideGraph_adj n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarFiniteStarToHexBuffered n y ≠
        triHexPlanarFiniteStarToHexBuffered n x :=
      fun h => hne ((triHexPlanarFiniteStarToHexBuffered n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarFiniteStar_boundary_of_outsideGraph_adj n psi y hadj


theorem triHexPlanarFiniteStar_outerBuffered_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex n)))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb (hexagonal.bufferedGraph (n + 2))
          (hexagonal.bufferedBoundary (n + 2)) p q rho) ≤
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (triHexPlanarFiniteStarGraph n)
          (triHexPlanarFiniteStarBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarFiniteStarToHexBuffered n).injective
    (triHexPlanarFiniteStarToHexBuffered_adjMatch n)
    (triHexPlanarFiniteStarBoundary n) hp hp1 hq
    (triHexPlanarFiniteStar_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h


end
end StatMech.FK.PeriodicPlanar
