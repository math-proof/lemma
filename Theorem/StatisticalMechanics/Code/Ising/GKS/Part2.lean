/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.GKS.Part2
open scoped BigOperators
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


omit [DecidableEq V] in
@[simp] lemma monomial_zero (s : ConfigSpace V) : monomial (0 : V → ℕ) s = 1 := by
  unfold monomial; simp

omit [DecidableEq V] in

lemma monomial_add (m₁ m₂ : V → ℕ) (s : ConfigSpace V) :
    monomial (m₁ + m₂) s = monomial m₁ s * monomial m₂ s := by
  unfold monomial
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => by rw [Pi.add_apply, pow_add])


lemma sum_monomial_nonneg (m : V → ℕ) : 0 ≤ ∑ s : ConfigSpace V, monomial m s := by
  have key : (∑ s : ConfigSpace V, monomial m s)
      = ∏ x : V, ∑ b : Bool, (spinB b) ^ (m x) := by
    unfold monomial
    simp_rw [spin_eq_spinB]
    rw [← Fintype.prod_sum (fun x b => (spinB b) ^ (m x))]
  rw [key]
  apply Finset.prod_nonneg
  intro x _
  rw [Fintype.sum_bool]
  show 0 ≤ (spinB true) ^ (m x) + (spinB false) ^ (m x)
  simp only [spinB]
  norm_num
  rcases Nat.even_or_odd (m x) with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num


end Ising
end StatMech
