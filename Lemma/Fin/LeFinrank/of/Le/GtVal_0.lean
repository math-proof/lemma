import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation
open GLnBuilding


/--
[schreierCell_finrank_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j j' : Fin (n + 1)}
-- given
  (hi : 0 < i.val)
  (hjj' : j ≤ j') :
-- imply
  Module.finrank k ↥(schreierCell σ τ i hi j) ≤ Module.finrank k ↥(schreierCell σ τ i hi j') :=
-- proof
  Submodule.finrank_mono (schreierCell_mono σ τ i hi j j' hjj')


/--
[existsUnique_step_jump](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma existsUnique_step_jump_eq
  [Field k]
  {n : ℕ}
  {n : ℕ}
  {g : Fin (n + 1) → ℕ}
-- given
  (hmono : Monotone g)
  (hstep : ∀ j : Fin n, g ⟨j.val + 1, by omega⟩ ≤ g ⟨j.val, by omega⟩ + 1)
  (htotal : g ⟨n, by omega⟩ = g ⟨0, by omega⟩ + 1) :
-- imply
  ∃! j : Fin n, g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 := by
-- proof
  apply GLnBuilding.existsUnique_step_jump g hmono hstep htotal

/--
[existsUnique_jump_col](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma existsUnique_jump_col_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  ∃! j : Fin n, Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) = Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1 := by
-- proof
  apply GLnBuilding.existsUnique_jump_col σ τ hσ hτ i hi

/--
[jumpCol_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jumpCol_spec_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) = Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩) + 1 := by
-- proof
  apply GLnBuilding.jumpCol_spec σ τ hσ hτ i hi

/--
[jumpCol_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jumpCol_unique_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j : Fin n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val)
  (hj : Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) = Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1) :
-- imply
  j = jumpCol σ τ hσ hτ i hi := by
-- proof
  apply GLnBuilding.jumpCol_unique σ τ hσ hτ i hi j hj

/--
[schreierCell_lt_at_jumpCol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma schreierCell_lt_at_jumpCol_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ < schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ := by
-- proof
  apply GLnBuilding.schreierCell_lt_at_jumpCol σ τ hσ hτ i hi

/--
[vi_inter_wj_not_le_vim1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma vi_inter_wj_not_le_vim1_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  ¬(σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ≤ σ.spaces ⟨i.val - 1, by omega⟩) := by
-- proof
  apply GLnBuilding.vi_inter_wj_not_le_vim1 σ τ hσ hτ i hi

/--
[exists_jhGapVector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma exists_jhGapVector_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  ∃ v : Vec k n, v ∈ σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ∧ v ∉ σ.spaces ⟨i.val - 1, by omega⟩ := by
-- proof
  apply GLnBuilding.exists_jhGapVector σ τ hσ hτ i hi

/--
[jhGapVector_mem_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jhGapVector_mem_inf_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  jhGapVector σ τ hσ hτ i hi ∈ σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ := by
-- proof
  apply GLnBuilding.jhGapVector_mem_inf σ τ hσ hτ i hi

/--
[jhGapVector_not_mem_lower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jhGapVector_not_mem_lower_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  jhGapVector σ τ hσ hτ i hi ∉ σ.spaces ⟨i.val - 1, by omega⟩ := by
-- proof
  apply GLnBuilding.jhGapVector_not_mem_lower σ τ hσ hτ i hi

/--
[jhGapVector_mem_Vi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jhGapVector_mem_Vi_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  jhGapVector σ τ hσ hτ i hi ∈ σ.spaces i := by
-- proof
  apply GLnBuilding.jhGapVector_mem_Vi σ τ hσ hτ i hi

/--
[jhGapVector_mem_Wj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jhGapVector_mem_Wj_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  jhGapVector σ τ hσ hτ i hi ∈ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ := by
-- proof
  apply GLnBuilding.jhGapVector_mem_Wj σ τ hσ hτ i hi

/--
[jhGapVector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean)
-/
private lemma jhGapVector_ne_zero_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  jhGapVector σ τ hσ hτ i hi ≠ 0 := by
-- proof
  apply GLnBuilding.jhGapVector_ne_zero σ τ hσ hτ i hi


-- created on 2026-10-23
-- updated on 2026-10-24
