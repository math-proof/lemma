/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs


/-- The set of multi-indices of order at most $N$ in $n$ variables is finite. -/
noncomputable instance multiIndexFintype (n N : ℕ) :
    Fintype { α : MultiIndex' n // multiIndexOrder α ≤ N } := by
  classical
  have h : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ i, α.1 i < N + 1 := by
    intro ⟨α, hα⟩ i
    simp only
    have hi : α i ≤ ∑ j : Fin n, α j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.lt_succ_of_le (le_trans hi hα)
  exact Fintype.ofInjective
    (fun ⟨α, hα⟩ => (fun i => ⟨α i, h ⟨α, hα⟩ i⟩ : Fin n → Fin (N + 1)))
    (by
      intro ⟨α₁, h₁⟩ ⟨α₂, h₂⟩ heq
      simp only [Subtype.mk.injEq] at heq ⊢
      funext i
      have := congr_fun heq i
      simp only [Fin.mk.injEq] at this
      exact this)

