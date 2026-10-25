/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.HighTemp
open scoped BigOperators
open Finset


namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ons_X_pos (x : ℝ) (hx : 0 ≤ x) : 0 < ons_X G x := by
  unfold ons_X
  have hmem : (∅ : Finset (Sym2 V)) ∈
      G.edgeFinset.powerset.filter IsEvenSubgraph := by
    rw [Finset.mem_filter]
    refine ⟨Finset.empty_mem_powerset _, ?_⟩
    intro v
    have : incCount (∅ : Finset (Sym2 V)) v = 0 := by
      unfold incCount
      simp
    rw [this]
    exact ⟨0, rfl⟩
  have hle : (1 : ℝ) ≤
      ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card := by
    have hterm : x ^ (∅ : Finset (Sym2 V)).card = 1 := by simp
    calc (1 : ℝ) = x ^ (∅ : Finset (Sym2 V)).card := hterm.symm
      _ ≤ ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card := by
          apply Finset.single_le_sum (f := fun F => x ^ F.card) ?_ hmem
          intro F _
          exact pow_nonneg hx _
  exact lt_of_lt_of_le zero_lt_one hle


end Onsager
end StatMech
