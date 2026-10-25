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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part11
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarTriBufferedToFiniteTerminal_adjMatch (n : Nat) :
    ocd_AdjMatch (triangular.bufferedGraph n)
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel n))
      (triHexPlanarTriBufferedToFiniteTerminal n) := by
  intro x y
  rfl

theorem triHexPlanarTriBufferedToFiniteTerminal_not_boundary
    (n : Nat) (v : triangular.BufferedVertex n) :
    ¬ triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n)
      (triHexPlanarTriBufferedToFiniteTerminal n v) := by
  rintro ⟨i, hi⟩
  apply hi
  apply box_mono 2 (show triangular.bufferedRadius n + 1 ≤
    triHexPlanarTriBufferedOuterLevel n by
      unfold triHexPlanarTriBufferedOuterLevel
      exact Nat.succ_le_succ
        (triangular.bufferedRadius_strictMono.monotone (Nat.le_succ n)))
  have hv : v.1 ∈ box 2 (triangular.bufferedRadius n) := by
    rw [← triangular_mem_orbitBox_iff_box]
    exact v.2
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarTriBufferedToFiniteTerminal, hexagonalStep] at hv ⊢ <;>
    omega

theorem triHexPlanarTriBufferedToFiniteTerminal_cross_boundary
    (n : Nat) (x : triangular.BufferedVertex n)
    (c : TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n))
    (hadj : (triHexPlanarFiniteTriangleInducedGraph
      (triHexPlanarTriBufferedOuterLevel n)).Adj
        (triHexPlanarTriBufferedToFiniteTerminal n x) c)
    (hc : c ∉ Set.range (triHexPlanarTriBufferedToFiniteTerminal n)) :
    triangular.bufferedBoundary n x := by
  refine ⟨c.1, hadj, ?_⟩
  intro hcbox
  apply hc
  exact ⟨⟨c.1, hcbox⟩, Subtype.ext rfl⟩

theorem triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal
        (triHexPlanarTriBufferedOuterLevel n))))
    (x : triangular.BufferedVertex n)
    {c : TriHexPlanarFiniteTerminal
      (triHexPlanarTriBufferedOuterLevel n)}
    (h : (ocd_outsideGraph
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel n))
      (triHexPlanarTriBufferedToFiniteTerminal n)
      (triHexPlanarFiniteBoundary
        (triHexPlanarTriBufferedOuterLevel n)) psi).Adj
        (triHexPlanarTriBufferedToFiniteTerminal n x) c) :
    triangular.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · apply triHexPlanarTriBufferedToFiniteTerminal_cross_boundary
      n x c hadj
    rintro ⟨z, hz⟩
    apply hnotRange
    refine ⟨s(x, z), ?_⟩
    rw [ocd_innerEdge_mk]
    congr 1
  · exact (triHexPlanarTriBufferedToFiniteTerminal_not_boundary
      n x houter).elim

theorem triHexPlanarTriBuffered_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal
        (triHexPlanarTriBufferedOuterLevel n)))) :
    ocd_inducedWiring
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel n))
        (triHexPlanarTriBufferedToFiniteTerminal n)
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel n)) psi ≤
      boundaryCliqueGraph (triangular.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarTriBufferedToFiniteTerminal n x ≠
        triHexPlanarTriBufferedToFiniteTerminal n y :=
      fun h => hne ((triHexPlanarTriBufferedToFiniteTerminal n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
        n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarTriBufferedToFiniteTerminal n y ≠
        triHexPlanarTriBufferedToFiniteTerminal n x :=
      fun h => hne ((triHexPlanarTriBufferedToFiniteTerminal n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
        n psi y hadj


theorem triHexPlanarTriBuffered_outerTriangle_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (triangular.BufferedVertex n)))} (hA : IsIncreasing A) :
    finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel n))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel n)) p q
        (ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal n) ⁻¹' A) ≤
      finiteWiredEventMass (triangular.bufferedGraph n)
        (triangular.bufferedBoundary n) p q A := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarTriBufferedToFiniteTerminal n).injective
    (triHexPlanarTriBufferedToFiniteTerminal_adjMatch n)
    (triangular.bufferedBoundary n) hp hp1 hq
    (triHexPlanarTriBuffered_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb, finiteWiredEventMass] using h


end
end StatMech.FK.PeriodicPlanar
