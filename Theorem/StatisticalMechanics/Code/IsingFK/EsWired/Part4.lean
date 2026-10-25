/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part3
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem pottsProbWired_nonneg (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    0 ≤ pottsProbWired G bdry q b β J σ := by
  unfold pottsProbWired pottsWeightWired
  apply div_nonneg _ (pottsZWired_pos G bdry q b β J).le
  split
  · exact Potts.pottsWeight_nonneg G β J σ
  · rfl


theorem pottsProbWired_sum_eq_one (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    (∑ σ : V → Fin q, pottsProbWired G bdry q b β J σ) = 1 := by
  unfold pottsProbWired
  rw [← Finset.sum_div]
  exact div_self (pottsZWired_ne_zero G bdry q b β J)


theorem pottsProbWired_eq_conditional {q : ℕ} [NeZero q] (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    pottsProbWired G bdry q b β J σ
      = if BoundaryFixed bdry b σ then
          Potts.pottsProb G q β J σ /
            (∑ τ : V → Fin q,
              if BoundaryFixed bdry b τ then Potts.pottsProb G q β J τ else 0)
        else 0 := by
  unfold pottsProbWired pottsWeightWired pottsZWired pottsWeightWired Potts.pottsProb
  have hZpos : 0 < Potts.pottsZ G q β J := Potts.pottsZ_pos G q β J
  have hden : (∑ τ : V → Fin q,
        if BoundaryFixed bdry b τ then Potts.pottsWeight G β J τ / Potts.pottsZ G q β J else 0)
      = (∑ τ : V → Fin q, if BoundaryFixed bdry b τ then Potts.pottsWeight G β J τ else 0)
          / Potts.pottsZ G q β J := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro τ _; split <;> simp
  rw [hden]
  by_cases h : BoundaryFixed bdry b σ
  · rw [if_pos h, if_pos h, div_div_div_cancel_right₀]
    exact hZpos.ne'
  · rw [if_neg h, if_neg h, zero_div]


end IsingFK
end StatMech
