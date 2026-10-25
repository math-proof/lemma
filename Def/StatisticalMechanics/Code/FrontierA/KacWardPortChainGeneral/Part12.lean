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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part11
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedPortForestCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) :
    Fin (Fintype.card V * (Fintype.card (KWDartPort G) + 1)) := by
  let block := Fintype.card (KWDartPort G) + 1
  let vertexRank := (Fintype.equivFin V p.1).val
  let portRank := kwOrderedPortRank order p
  have hport : portRank < block := by
    have hp := (order p.1 p.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G p.1
    dsimp only [portRank, block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  refine ⟨vertexRank * block + portRank, ?_⟩
  calc
    vertexRank * block + portRank < vertexRank * block + block :=
      Nat.add_lt_add_left hport _
    _ = (vertexRank + 1) * block := by rw [Nat.succ_mul]
    _ ≤ Fintype.card V * block := by
      exact Nat.mul_le_mul_right block (Fintype.equivFin V p.1).isLt

end StatMech.FrontierA
