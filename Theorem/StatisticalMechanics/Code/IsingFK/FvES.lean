/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem sum_eval_factor {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (a₀ : A) (F : B → ℝ) :
    (∑ g : A → B, F (g a₀))
      = (Fintype.card ({a : A // a ≠ a₀} → B)) • (∑ b : B, F b) := by
  classical
  let e : (A → B) ≃ (B × ({a : A // a ≠ a₀} → B)) :=
  { toFun := fun g => (g a₀, fun a => g a.1)
    invFun := fun p => fun a => if h : a = a₀ then p.1 else p.2 ⟨a, h⟩
    left_inv := by intro g; funext a; by_cases h : a = a₀ <;> simp [h]
    right_inv := by rintro ⟨b, h⟩; ext
                    · simp
                    · simp only; rename_i a; rw [dif_neg a.2] }
  have hcomp : (∑ g : A → B, F (g a₀)) = ∑ p : B × ({a : A // a ≠ a₀} → B), F p.1 := by
    rw [← e.sum_comp (fun p => F p.1)]; rfl
  rw [hcomp, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]


end IsingFK
end StatMech
