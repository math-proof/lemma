/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
import Def.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- Defining property: at column $j = $ `jumpCol`, the Schreier cell dimension jumps by exactly $1$. -/
theorem jumpCol_spec (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) =
    Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩) + 1 :=
  (existsUnique_jump_col σ τ hσ hτ i hi).exists.choose_spec

/-- Uniqueness: any column where the Schreier cell dimension jumps must equal `jumpCol`. -/
theorem jumpCol_unique (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j : Fin n)
    (hj : Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) =
          Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1) :
    j = jumpCol σ τ hσ hτ i hi := by
  exact (existsUnique_jump_col σ τ hσ hτ i hi).unique hj (jumpCol_spec σ τ hσ hτ i hi)

/-- At the jump column, the Schreier cell strictly increases. -/
theorem schreierCell_lt_at_jumpCol (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ <
    schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ := by
  set jc := jumpCol σ τ hσ hτ i hi
  apply lt_of_le_of_ne
  · exact schreierCell_mono σ τ i hi ⟨jc.val, by omega⟩ ⟨jc.val + 1, by omega⟩
      (Fin.mk_le_mk.mpr (by omega))
  · intro heq
    have hspec := jumpCol_spec σ τ hσ hτ i hi
    rw [heq] at hspec
    omega

/-- Key non-containment: $V_i \cap W_{j+1}$ is not contained in $V_{i-1}$ at the jump column $j$,
ensuring existence of the Jordan-Hölder gap vector. -/
theorem vi_inter_wj_not_le_vim1 (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ¬(σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ≤
      σ.spaces ⟨i.val - 1, by omega⟩) := by
  intro hle
  have hlt := schreierCell_lt_at_jumpCol σ τ hσ hτ i hi

  have heq_sup : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ ⊔
        (σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) :=
    schreierCell_eq_sup σ τ i hi _

  have hsup_eq : σ.spaces ⟨i.val - 1, by omega⟩ ⊔
      (σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) =
      σ.spaces ⟨i.val - 1, by omega⟩ := sup_eq_left.mpr hle

  have hcell_eq_vim1 : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ := by rw [heq_sup, hsup_eq]
  have hzero : schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ := schreierCell_zero σ τ i hi

  have hle_cell : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ≤
      schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ := by
    rw [hcell_eq_vim1, ← hzero]
    exact schreierCell_mono σ τ i hi ⟨0, Nat.zero_lt_succ n⟩
      ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
  exact absurd hle_cell (not_le_of_gt hlt)

/-- Existence of a Jordan-Hölder gap vector: a vector $v \in V_i \cap W_{j+1}$ with $v \notin V_{i-1}$. -/
theorem exists_jhGapVector (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ∃ v : Vec k n,
      v ∈ σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ∧
      v ∉ σ.spaces ⟨i.val - 1, by omega⟩ := by
  have hle := vi_inter_wj_not_le_vim1 σ τ hσ hτ i hi
  rw [SetLike.not_le_iff_exists] at hle
  exact hle

end GLnBuilding
