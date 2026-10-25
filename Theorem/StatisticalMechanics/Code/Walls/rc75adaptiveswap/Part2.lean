/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem coordSwap_involutive (i : Fin n) (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
    [DecidablePred pred] (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
    Function.Involutive (coordSwap i pred) := by
  intro p
  unfold coordSwap
  by_cases h : pred p
  · rw [if_pos h]
    have h2 : pred (swapAt i p) := (horb p).mpr h
    rw [if_pos h2, swapAt_involutive i p]
  · rw [if_neg h, if_neg h]


theorem coordSwap_bijective (i : Fin n) (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
    [DecidablePred pred] (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
    Function.Bijective (coordSwap i pred) :=
  (coordSwap_involutive i pred horb).bijective


theorem swapAt_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K : Finset (Fin n)} {i : Fin n} (hKi : Disjoint K {i}) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
    (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · apply hA
    intro e he
    have hei : e ≠ i := by
      intro h; subst h
      exact (Finset.disjoint_left.mp hKi he) (Finset.mem_singleton_self _)
    exact (swapAt_off i (ω₁, ω₂) hei).1
  · apply hB
    intro e he
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at he
    rw [he]
    exact (swapAt_on i (ω₁, ω₂)).2


end StatMech.Walls
