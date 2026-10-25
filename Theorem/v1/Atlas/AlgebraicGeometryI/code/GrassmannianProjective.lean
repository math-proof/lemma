/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra


namespace GrassmannianProjective

/-- Any order embedding `Fin n ↪o Fin n` is the identity, since a strictly increasing bijection
on `Fin n` must be the identity. -/
lemma orderEmb_fin_eq_id (n : ℕ) (f : Fin n ↪o Fin n) (i : Fin n) : f i = i := by
  have hf := f.strictMono
  have h_surj : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h_ge : ∀ j : Fin n, (j : ℕ) ≤ (f j : ℕ) := by
    intro ⟨j, hj⟩
    induction j with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := Nat.lt_of_succ_lt hj
      have hih := ih hk
      have hlt : (f ⟨k, hk⟩ : ℕ) < (f ⟨k + 1, hj⟩ : ℕ) :=
        hf (show (⟨k, hk⟩ : Fin n) < ⟨k + 1, hj⟩ by simp [Fin.lt_def])
      simp only at hih hlt ⊢; omega
  have h_le : ∀ j : Fin n, (f j : ℕ) ≤ (j : ℕ) := by
    by_contra h; push Not at h; obtain ⟨j, hj⟩ := h
    set e := Equiv.ofBijective f ⟨f.injective, h_surj⟩
    have hsum : ∑ i : Fin n, (f i : ℕ) = ∑ i : Fin n, (i : ℕ) := by
      conv_rhs => rw [show (fun i : Fin n => (i : ℕ)) =
        (fun i => (e (e.symm i) : ℕ)) from by ext; simp]
      rw [← Equiv.sum_comp e.symm]; simp [e, Equiv.ofBijective]
    exact absurd hsum (Nat.ne_of_gt
      (Finset.sum_lt_sum (fun i _ => h_ge i) ⟨j, Finset.mem_univ j, by omega⟩))
  exact Fin.ext (Nat.le_antisymm (h_le i) (h_ge i))

variable {K : Type*} [Field K]

/-- The exterior power of a basis is nonzero: `e_1 ∧ ... ∧ e_n ≠ 0`. -/
lemma ιMulti_basis_ne_zero {n : ℕ} {W : Type*} [AddCommGroup W] [Module K W]
    (b : Module.Basis (Fin n) K W) :
    (exteriorPower.ιMulti K n (fun i => b i)) ≠ 0 := by
  intro h
  set s : Set.powersetCard (Fin n) n := ⟨Finset.univ, Finset.card_fin n⟩
  have hdiag := exteriorPower.ιMultiDual_apply_diag K n b s
  have key : exteriorPower.ιMulti_family K n (⇑b) s =
      exteriorPower.ιMulti K n (fun i => b i) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id n (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag
  rw [show exteriorPower.ιMulti K n (fun i => b i) = (0 : ↥(⋀[K]^n W)) from
    Subtype.val_injective (by simp [h]), map_zero] at hdiag
  exact zero_ne_one hdiag

end GrassmannianProjective
