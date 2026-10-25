/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Def.StatisticalMechanics.Code.Ising.KramersWannierClose
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section LowTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in


theorem sum_bond_eq_card_sub_two_cut (s : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond s e)
      = (G.edgeFinset.card : ℝ) - 2 * (cutEdges G s).card := by
  unfold cutEdges
  rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => bond s e = -1)]
  have h1 : ∑ e ∈ G.edgeFinset.filter (fun e => bond s e = -1), bond s e
      = - (G.edgeFinset.filter (fun e => bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2)]; simp
  have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬ bond s e = -1), bond s e
      = (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_]; · simp
    intro e he
    rcases bond_eq_one_or_neg_one s e with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp he).2
  rw [h1, h2]
  have hcard : (G.edgeFinset.filter (fun e => bond s e = -1)).card
      + (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  push_cast [← hcard]
  ring


theorem isingZ_low_temp_expansion (β : ℝ) :
    isingZ G β 0
      = Real.exp (β * G.edgeFinset.card)
        * ∑ s : ConfigSpace V, Real.exp (-2 * β) ^ (cutEdges G s).card := by
  unfold isingZ isingWeight hamiltonian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [zero_mul, sub_zero]
  rw [sum_bond_eq_card_sub_two_cut G s, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring


omit [Fintype V] [DecidableEq V] in

theorem bond_flip (s : ConfigSpace V) (e : Sym2 V) :
    bond (fun v => ! s v) e = bond s e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk, bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

omit [DecidableEq V] in


theorem cutEdges_flip (s : ConfigSpace V) :
    cutEdges G (fun v => ! s v) = cutEdges G s := by
  unfold cutEdges
  apply Finset.filter_congr
  intro e _
  rw [bond_flip]

end LowTemp
end Ising
end StatMech
