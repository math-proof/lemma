/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc9core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc16_climbUp (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 + (k : ℤ)] := by
  induction k with
  | zero =>
    have h0 : (![z 0, z 1 + ((0 : ℕ) : ℤ)] : Site 2) = z := by ext i; fin_cases i <;> simp
    rw [h0]
  | succ n ih =>
    have hstep := ih (fun j hj => hoff j (by omega))
    have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 + (n : ℤ)] : Site 2)
        ![z 0, z 1 + ((n + 1 : ℕ) : ℤ)] := by
      have h := sw_adj_vertSucc (z 0) (z 1 + (n : ℤ))
      have heq : (![z 0, z 1 + (n : ℤ) + 1] : Site 2) = ![z 0, z 1 + ((n + 1 : ℕ) : ℤ)] := by
        ext i; fin_cases i <;> simp; ring
      rwa [heq] at h
    exact hstep.trans
      (Adj.reachable ⟨hadj, hoff n (by omega), hoff (n + 1) (by omega)⟩ :
        (offSupport Vc).Reachable _ _)


theorem kc16_climbDown (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 - (k : ℤ)] := by
  induction k with
  | zero =>
    have h0 : (![z 0, z 1 - ((0 : ℕ) : ℤ)] : Site 2) = z := by ext i; fin_cases i <;> simp
    rw [h0]
  | succ n ih =>
    have hstep := ih (fun j hj => hoff j (by omega))
    have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 - ((n + 1 : ℕ) : ℤ)] : Site 2)
        ![z 0, z 1 - (n : ℤ)] := by
      have h := sw_adj_vertSucc (z 0) (z 1 - ((n + 1 : ℕ) : ℤ))
      have heq : (![z 0, z 1 - ((n + 1 : ℕ) : ℤ) + 1] : Site 2) = ![z 0, z 1 - (n : ℤ)] := by
        ext i; fin_cases i <;> simp; ring
      rwa [heq] at h
    exact hstep.trans
      (Adj.reachable ⟨hadj.symm, hoff n (by omega), hoff (n + 1) (by omega)⟩ :
        (offSupport Vc).Reachable _ _)


theorem kc16_climbUp_step (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support)
    (hright : (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have hclimb := kc16_climbUp Vc z k hoff
  have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 + (k : ℤ)] : Site 2)
      ![z 0 + 1, z 1 + (k : ℤ)] := sw_adj_horizSucc (z 1 + (k : ℤ)) (z 0)
  exact ⟨![z 0 + 1, z 1 + (k : ℤ)], by simp,
    hclimb.trans (Adj.reachable ⟨hadj, hoff k (le_refl k), hright⟩ :
      (offSupport Vc).Reachable _ _)⟩


theorem kc16_climbDown_step (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support)
    (hright : (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have hclimb := kc16_climbDown Vc z k hoff
  have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 - (k : ℤ)] : Site 2)
      ![z 0 + 1, z 1 - (k : ℤ)] := sw_adj_horizSucc (z 1 - (k : ℤ)) (z 0)
  exact ⟨![z 0 + 1, z 1 - (k : ℤ)], by simp,
    hclimb.trans (Adj.reachable ⟨hadj, hoff k (le_refl k), hright⟩ :
      (offSupport Vc).Reachable _ _)⟩


end Walls
end StatMech
