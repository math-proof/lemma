/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section HighTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] in

lemma bond_eq_one_or_neg_one (s : ConfigSpace V) (e : Sym2 V) :
    bond s e = 1 ∨ bond s e = -1 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]


theorem exp_mul_eq_cosh_mul (β b : ℝ) (hb : b = 1 ∨ b = -1) :
    Real.exp (β * b) = Real.cosh β * (1 + Real.tanh β * b) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rcases hb with h | h
  · subst h
    rw [mul_one]; field_simp; rw [← Real.cosh_add_sinh]
  · subst h
    rw [show β * (-1) = -β by ring, Real.exp_neg]
    field_simp
    rw [show Real.cosh β + -Real.sinh β = Real.cosh β - Real.sinh β by ring,
      Real.cosh_sub_sinh, ← Real.exp_add, add_neg_cancel, Real.exp_zero]


omit [DecidableEq V] in


theorem isingWeight_field_free_eq_prod (β : ℝ) (s : ConfigSpace V) :
    isingWeight G β 0 s = ∏ e ∈ G.edgeFinset, Real.exp (β * bond s e) := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [show -β * -(∑ e ∈ G.edgeFinset, bond s e)
        = β * (∑ e ∈ G.edgeFinset, bond s e) by ring,
    Finset.mul_sum, Real.exp_sum]


omit [DecidableEq V] in


theorem prod_exp_bond_eq (β : ℝ) (s : ConfigSpace V) :
    (∏ e ∈ G.edgeFinset, Real.exp (β * bond s e))
      = (Real.cosh β) ^ G.edgeFinset.card
        * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [exp_mul_eq_cosh_mul β (bond s e) (bond_eq_one_or_neg_one s e)]


end HighTemp
end Ising
end StatMech
