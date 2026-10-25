/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem swapAt_involutive (i : Fin n) : Function.Involutive (swapAt i) := by
  intro p
  unfold swapAt
  ext j <;> simp only [] <;> split_ifs with h <;> subst_vars <;> rfl


theorem swapAt_bijective (i : Fin n) : Function.Bijective (swapAt i) :=
  (swapAt_involutive i).bijective


theorem swapAt_off (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ≠ i) : (swapAt i p).1 j = p.1 j ∧ (swapAt i p).2 j = p.2 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapAt, if_neg hj]


theorem swapAt_on (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    (swapAt i p).1 i = p.2 i ∧ (swapAt i p).2 i = p.1 i := by
  refine ⟨?_, ?_⟩ <;> simp only [swapAt, if_pos]


theorem swapAt_pair_perm (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) (j : Fin n) :
    ((swapAt i p).1 j, (swapAt i p).2 j) = (p.1 j, p.2 j)
      ∨ ((swapAt i p).1 j, (swapAt i p).2 j) = (p.2 j, p.1 j) := by
  by_cases hj : j = i
  · right; subst hj; simp only [swapAt, if_pos]
  · left; simp only [swapAt, if_neg hj]


end StatMech.Walls
