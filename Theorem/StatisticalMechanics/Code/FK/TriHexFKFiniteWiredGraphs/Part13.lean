/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part4
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStar_isolatedCenter_not_wired_adj
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteStarIsolatedCenter n omega)
    (v : TriHexPlanarFiniteStarVertex n) :
    ¬ (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj
        (Sum.inl z.1) v := by
  rw [wiredGraph_adj]
  rintro (hopen | hboundary)
  · obtain ⟨cell, i, hi, horient⟩ :=
      triHexPlanarFiniteStar_openSub_adj_eq_spoke n omega hopen
    rcases horient with ⟨hcenter, _⟩ | ⟨_, hcenter⟩
    · have hcell : cell = z.1 := Sum.inl.inj hcenter.symm
      subst cell
      rw [z.2] at hi
      fin_cases i <;> simp [triHexLocalDirection] at hi
    · have : Sum.inl z.1 = Sum.inr
          (triHexPlanarFiniteTerminalMap n cell i) := hcenter
      exact Sum.inl_ne_inr this
  · exact hboundary.2.1.elim


theorem triHexPlanarFiniteStar_wired_adj_representative_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable
      (triHexPlanarFiniteStarRepresentative n omega u)
      (triHexPlanarFiniteStarRepresentative n omega v) := by
  rw [wiredGraph_adj] at huv
  rcases huv with hopen | hboundary
  · exact (triHexPlanarFiniteStar_openSub_adj_representative_reachable
      n omega hopen).mono le_sup_left
  · rcases u with u | u <;> rcases v with v | v
    · exact hboundary.2.1.elim
    · exact hboundary.2.1.elim
    · exact hboundary.2.2.elim
    · apply SimpleGraph.Adj.reachable
      apply (show boundaryCliqueGraph (triHexPlanarFiniteBoundary n) ≤
        triHexPlanarFiniteStarWiredSectorGraph n omega from le_sup_right)
      rw [boundaryCliqueGraph_adj]
      exact ⟨fun huv => hboundary.1 (congrArg Sum.inr huv),
        hboundary.2.1, hboundary.2.2⟩


end
end StatMech.FK.PeriodicPlanar
