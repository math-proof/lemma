/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part10


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem hexagonalTorus_numClusters_eq_terminalSector_add_isolated
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    numClusters (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega) =
      Fintype.card (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent +
        Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
  unfold numClusters
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (hexagonalTorusConnectedComponentEquiv L omega)

section ActiveOdds

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem edgeProductW_extendActive_eq_activeProduct
    (pf : Sym2 V → ℝ) (omega : ConfigSpace G.edgeSet) :
    edgeProductW G pf (extendActive G omega) =
      ∏ e : G.edgeSet, if omega e then pf e.1 else 1 - pf e.1 := by
  unfold edgeProductW
  rw [Finset.prod_subtype (p := fun e => e ∈ G.edgeSet)
    G.edgeFinset (fun e => by
    simpa [SimpleGraph.mem_edgeFinset])]
  apply Fintype.prod_congr
  intro e
  rw [extendActive_apply]


theorem edgeProductW_extendActive_odds_factor
    (pf : Sym2 V → ℝ) (odds : G.edgeSet → ℝ)
    (h : ∀ e : G.edgeSet, pf e.1 = (1 - pf e.1) * odds e)
    (omega : ConfigSpace G.edgeSet) :
    edgeProductW G pf (extendActive G omega) =
      (∏ e : G.edgeSet, (1 - pf e.1)) *
        ∏ e : G.edgeSet, if omega e then odds e else 1 := by
  rw [edgeProductW_extendActive_eq_activeProduct]
  calc
    (∏ e : G.edgeSet, if omega e then pf e.1 else 1 - pf e.1) =
        ∏ e : G.edgeSet,
          (1 - pf e.1) * (if omega e then odds e else 1) := by
      apply Fintype.prod_congr
      intro e
      by_cases he : omega e
      · rw [if_pos he, if_pos he]
        exact h e
      · rw [if_neg he, if_neg he, mul_one]
    _ = (∏ e : G.edgeSet, (1 - pf e.1)) *
          ∏ e : G.edgeSet, if omega e then odds e else 1 := by
      rw [Finset.prod_mul_distrib]

end ActiveOdds
end StatMech.FK.PeriodicPlanar
