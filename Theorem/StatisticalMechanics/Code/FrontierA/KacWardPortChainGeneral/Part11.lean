/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOutgoingDart_card_le_port_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card (KWOutgoingDart (G := G) v) ≤
      Fintype.card (KWDartPort G) := by
  let f : KWOutgoingDart (G := G) v → KWDartPort G := fun d ↦
    ⟨v, Fintype.equivFin (KWOutgoingDart (G := G) v) d⟩
  apply Fintype.card_le_of_injective f
  intro d e h
  have hindex : Fintype.equivFin (KWOutgoingDart (G := G) v) d =
      Fintype.equivFin (KWOutgoingDart (G := G) v) e := by
    exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  exact (Fintype.equivFin (KWOutgoingDart (G := G) v)).injective hindex


end StatMech.FrontierA
