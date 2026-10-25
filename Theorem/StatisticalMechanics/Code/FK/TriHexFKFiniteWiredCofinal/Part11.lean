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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part10
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangleToBuffered_adjMatch (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteTriangleInducedGraph n)
      (triangular.bufferedGraph (n + 2))
      (triHexPlanarFiniteTriangleToBuffered n) := by
  intro x y
  rfl

theorem triHexPlanarFiniteTriangleToBuffered_not_boundary
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    ¬ triangular.bufferedBoundary (n + 2)
      (triHexPlanarFiniteTriangleToBuffered n v) := by
  let vPrev : triangular.BufferedVertex (n + 1) :=
    ⟨v.1, by
      apply triangular.orbitBox_mono (triangular.id_le_bufferedRadius (n + 1))
      exact triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ n v⟩
  have hnot := triangular.not_bufferedBoundary_incl_succ (n + 1) vPrev
  simpa [triHexPlanarFiniteTriangleToBuffered, vPrev, Nat.add_assoc] using hnot

theorem triHexPlanarFiniteTriangleToBuffered_cross_boundary
    (n : Nat) (v : TriHexPlanarFiniteTerminal n)
    (c : triangular.BufferedVertex (n + 2))
    (hadj : (triangular.bufferedGraph (n + 2)).Adj
      (triHexPlanarFiniteTriangleToBuffered n v) c)
    (hc : c ∉ Set.range (triHexPlanarFiniteTriangleToBuffered n)) :
    triHexPlanarFiniteBoundary n v := by
  apply triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal n v c.1 hadj
  intro hcTerm
  apply hc
  exact ⟨⟨c.1, hcTerm⟩, Subtype.ext rfl⟩

theorem triHexPlanarFiniteTriangle_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (triangular.BufferedVertex (n + 2)))) :
    ocd_inducedWiring (triangular.bufferedGraph (n + 2))
        (triHexPlanarFiniteTriangleToBuffered n)
        (triangular.bufferedBoundary (n + 2)) psi ≤
      boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarFiniteTriangleToBuffered n x ≠
        triHexPlanarFiniteTriangleToBuffered n y :=
      fun h => hne ((triHexPlanarFiniteTriangleToBuffered n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · rw [ocd_outsideGraph_adj] at hadj
      rcases hadj with ⟨ha, _, hr⟩ | ⟨_, hb, _⟩
      · exact triHexPlanarFiniteTriangleToBuffered_cross_boundary n x c ha
          (by rintro ⟨z, hz⟩; exact hr ⟨s(x, z), by
            rw [ocd_innerEdge_mk]; congr 1⟩)
      · exact (triHexPlanarFiniteTriangleToBuffered_not_boundary n x hb).elim
  · have hreach' := hreach.symm
    have hne' : triHexPlanarFiniteTriangleToBuffered n y ≠
        triHexPlanarFiniteTriangleToBuffered n x :=
      fun h => hne ((triHexPlanarFiniteTriangleToBuffered n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · rw [ocd_outsideGraph_adj] at hadj
      rcases hadj with ⟨ha, _, hr⟩ | ⟨_, hb, _⟩
      · exact triHexPlanarFiniteTriangleToBuffered_cross_boundary n y c ha
          (by rintro ⟨z, hz⟩; exact hr ⟨s(y, z), by
            rw [ocd_innerEdge_mk]; congr 1⟩)
      · exact (triHexPlanarFiniteTriangleToBuffered_not_boundary n y hb).elim

theorem triHexPlanarFiniteTriangle_outerBuffered_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal n)))} (hA : IsIncreasing A) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹' A) ≤
      finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q A := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarFiniteTriangleToBuffered n).injective
    (triHexPlanarFiniteTriangleToBuffered_adjMatch n)
    (triHexPlanarFiniteBoundary n) hp hp1 hq
    (triHexPlanarFiniteTriangle_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb, finiteWiredEventMass] using h

end
end StatMech.FK.PeriodicPlanar
