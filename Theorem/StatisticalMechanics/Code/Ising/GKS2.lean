/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


omit [Fintype V] in


lemma spinProd_mul_self (A B : Finset V) (s : ConfigSpace V) :
    spinProd A s * spinProd B s = spinProd (A ∆ B) s := by
  classical
  unfold spinProd
  have h1 : (∏ x ∈ A, spin s x) * (∏ x ∈ B, spin s x)
      = (∏ x ∈ A ∪ B, spin s x) * (∏ x ∈ A ∩ B, spin s x) :=
    (Finset.prod_union_inter).symm
  have hdisj : Disjoint (A ∆ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_symmDiff] at hx
    rw [Finset.mem_inter] at hx2
    rcases hx with ⟨_, hb⟩ | ⟨_, ha⟩
    · exact hb hx2.2
    · exact ha hx2.1
  have hunion : A ∪ B = (A ∆ B) ∪ (A ∩ B) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
    tauto
  have h2 : (∏ x ∈ A ∪ B, spin s x) = (∏ x ∈ A ∆ B, spin s x) * (∏ x ∈ A ∩ B, spin s x) := by
    rw [hunion, Finset.prod_union hdisj]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  have : (∏ x ∈ A ∩ B, spin s x * spin s x) = 1 :=
    Finset.prod_eq_one (fun x _ => spin_sq s x)
  rw [this, mul_one]


end Ising
end StatMech
