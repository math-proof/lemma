/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamilton


namespace TournamentHamilton

variable {n : ℕ}

/-- The finset of all Hamilton-path permutations of $T$. -/
noncomputable def Tournament.hamiltonPaths (T : Tournament (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter T.IsHamiltonPath

/-- The finset of all Hamilton-cycle permutations of $T$. -/
noncomputable def Tournament.hamiltonCycles (T : Tournament (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter T.IsHamiltonCycle

/-- Number of Hamilton paths of $T$. -/
noncomputable def numHamiltonPaths (T : Tournament (Fin n)) : ℕ :=
  T.hamiltonPaths.card

/-- Number of Hamilton cycles of $T$. -/
noncomputable def numHamiltonCycles (T : Tournament (Fin n)) : ℕ :=
  T.hamiltonCycles.card

/-- Extension of a tournament on $\mathrm{Fin}\, n$ to one on $\mathrm{Fin}(n+1)$ by adding
a new vertex whose incoming/outgoing edges are dictated by a Boolean function $f$:
$f(v) = \mathrm{true}$ means new vertex beats $v$. -/
def extendTournament (T : Tournament (Fin n)) (f : Fin n → Bool) :
    Tournament (Fin (n + 1)) where
  edge u v :=
    if hu : u.val < n then
      if hv : v.val < n then
        T.edge ⟨u.val, hu⟩ ⟨v.val, hv⟩
      else
        !(f ⟨u.val, hu⟩)
    else
      if hv : v.val < n then
        f ⟨v.val, hv⟩
      else
        false
  edge_irrefl v := by
    split_ifs with hu hv
    · exact T.edge_irrefl ⟨v.val, hu⟩
    · rfl
  edge_complete u v huv := by
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [dif_pos hu, dif_pos hv]
      have hne : (⟨u.val, hu⟩ : Fin n) ≠ ⟨v.val, hv⟩ := by
        intro h; apply huv; exact Fin.ext (by simpa using congrArg Fin.val h)
      exact T.edge_complete _ _ hne
    · simp only [dif_pos hu, dif_neg hv, dif_pos hu]
      cases f ⟨u.val, hu⟩ <;> simp
    · simp only [dif_neg hu, dif_pos hv, dif_neg hu]
      cases f ⟨v.val, hv⟩ <;> simp
    · exfalso; apply huv; exact Fin.ext (by omega)
  edge_asymm u v := by
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [dif_pos hu, dif_pos hv]
      exact T.edge_asymm _ _
    · simp only [dif_pos hu, dif_neg hv, dif_neg hv, dif_pos hu]
      intro h; simp [Bool.not_eq_true'] at h; exact h
    · simp only [dif_neg hu, dif_pos hv, dif_pos hv, dif_neg hu]
      intro h; simp [h]
    · simp only [dif_neg hu, dif_neg hv]
      intro h; exact absurd h Bool.false_ne_true

end TournamentHamilton
