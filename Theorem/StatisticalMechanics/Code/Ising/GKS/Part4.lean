/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.GKS.Part4
open scoped BigOperators
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] in
@[simp] lemma spinProd_empty (s : ConfigSpace V) : spinProd (∅ : Finset V) s = 1 := by
  simp [spinProd]

lemma isSpinMonomial_spinProd (A : Finset V) : IsSpinMonomial (spinProd A) := by
  classical
  refine ⟨fun x => if x ∈ A then 1 else 0, fun s => ?_⟩
  unfold spinProd monomial
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ A)
      (fun x => (spin s x) ^ (if x ∈ A then 1 else 0))]
  have h1 : (∏ x ∈ univ.filter (· ∈ A), (spin s x) ^ (if x ∈ A then 1 else 0))
      = ∏ x ∈ A, spin s x := by
    rw [Finset.filter_mem_eq_inter, univ_inter]
    exact Finset.prod_congr rfl (fun x hx => by rw [if_pos hx, pow_one])
  have h2 : (∏ x ∈ univ.filter (¬ · ∈ A), (spin s x) ^ (if x ∈ A then 1 else 0)) = 1 :=
    Finset.prod_eq_one (fun x hx => by
      rw [Finset.mem_filter] at hx; rw [if_neg hx.2, pow_zero])
  rw [h1, h2, mul_one]


end Ising
end StatMech
