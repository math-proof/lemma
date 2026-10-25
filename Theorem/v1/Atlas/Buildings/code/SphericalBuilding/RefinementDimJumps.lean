/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.SchreierRefinement
import Lemma.Fin.SchreierCell_0.eq.SpacesSubVal1.of.GtVal_0
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ModularLattice
import Def.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- Decomposition of the Schreier cell: $C_{i,j} = V_{i-1} + (V_i \cap W_j)$. -/
theorem schreierCell_eq_sup (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) (j : Fin (n + 1)) :
    schreierCell σ τ i hi j =
      σ.spaces ⟨i.val - 1, by omega⟩ ⊔ (σ.spaces i ⊓ τ.spaces j) := by
  unfold schreierCell
  have hle : σ.spaces ⟨i.val - 1, by omega⟩ ≤ σ.spaces i := by
    apply σ.monotone; simp only [Fin.le_iff_val_le_val]; omega
  conv_lhs => rw [sup_comm]
  rw [← inf_sup_assoc_of_le (τ.spaces j) hle, sup_comm]

/-- **Step bound**: along each column of the Schreier refinement, the dimension increases by at
most $1$ when moving from $W_j$ to $W_{j+1}$. -/
theorem schreierCell_finrank_step (σ τ : CompleteFlag k n)
    (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j : Fin n) :
    Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) ≤
    Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1 := by
  unfold schreierCell
  set A := σ.spaces ⟨i.val - 1, by omega⟩
  set C := σ.spaces i
  set B := τ.spaces ⟨j.val, by omega⟩
  set B' := τ.spaces ⟨j.val + 1, by omega⟩
  have hBB' : B ≤ B' := τ.monotone (by simp [Fin.le_iff_val_le_val])
  have hdim : Module.finrank k ↥B' ≤ Module.finrank k ↥B + 1 := by
    rw [hτ ⟨j.val + 1, by omega⟩, hτ ⟨j.val, by omega⟩]

  have hle : A ⊔ B ≤ A ⊔ B' := sup_le_sup_left hBB' A
  have hsup : Module.finrank k ↥(A ⊔ B') ≤ Module.finrank k ↥(A ⊔ B) + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B'
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h3 := Submodule.finrank_mono (inf_le_inf_left A hBB')
    omega

  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ (A ⊔ B')) (A ⊔ B)
  have h2 : (C ⊓ (A ⊔ B')) ⊓ (A ⊔ B) = C ⊓ (A ⊔ B) := by
    rw [inf_assoc, inf_eq_right.mpr hle]
  have h3 : (C ⊓ (A ⊔ B')) ⊔ (A ⊔ B) ≤ A ⊔ B' :=
    sup_le inf_le_right hle
  rw [h2] at h1
  have h4 := Submodule.finrank_mono h3
  omega

/-- **Total row jump**: in each row $i$ of the Schreier refinement, the dimension increases by
exactly $1$ from the leftmost cell ($V_{i-1}$) to the rightmost ($V_i$). -/
theorem schreierCell_row_total (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    Module.finrank k ↥(schreierCell σ τ i hi ⟨n, Nat.lt_succ_of_le le_rfl⟩) =
    Module.finrank k ↥(schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩) + 1 := by
  rw [schreierCell_last, schreierCell_zero]
  rw [hσ i, hσ ⟨i.val - 1, by omega⟩]
  simp
  omega

end GLnBuilding
