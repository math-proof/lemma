import Mathlib
import sympy.Basic


/--
[Subgroup_exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero.lean)
-/
@[path]
private lemma main
  [Group G]
  {H K N₀ : Subgroup G}
-- given
  (hHK : H ≤ K)
  (hHidx : H.relIndex K ≠ 0)
  (hN₀ : N₀ ≤ H)
  (hN₀idx : N₀.relIndex H ≠ 0)
  (htf : ∀ g ∈ N₀, IsOfFinOrder g → g = 1) :
-- imply
  ∃ N : Subgroup G, N ≤ N₀ ∧ (N.subgroupOf K).Normal ∧ N.relIndex H ≠ 0 ∧ ∀ g ∈ N, IsOfFinOrder g → g = 1 := by
-- proof
  classical

  let N₀' : Subgroup K := N₀.subgroupOf K
  have hN₀K : N₀.relIndex K ≠ 0 := by
    rw [← Subgroup.relIndex_mul_relIndex N₀ H K hN₀ hHK]
    exact mul_ne_zero hN₀idx hHidx
  have : N₀'.FiniteIndex := ⟨hN₀K⟩
  let C : Subgroup K := N₀'.normalCore
  have hCfin : C.FiniteIndex := inferInstance
  let N : Subgroup G := C.map K.subtype
  have hNK : N.subgroupOf K = C := Subgroup.comap_map_eq_self_of_injective K.subtype_injective C
  have hNle : N ≤ N₀ := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact Subgroup.normalCore_le N₀' hk
  have hNleK : N ≤ K := fun g hg => by obtain ⟨k, -, rfl⟩ := hg; exact k.2
  refine ⟨N, hNle, ?_, ?_, fun g hg hfin => htf g (hNle hg) hfin⟩
  · rw [hNK]; infer_instance
  · have h1 : N.relIndex K ≠ 0 := by
      show (N.subgroupOf K).index ≠ 0
      rw [hNK]; exact hCfin.index_ne_zero
    rw [← Subgroup.relIndex_mul_relIndex N H K (hNle.trans hN₀) hHK] at h1
    exact left_ne_zero_of_mul h1


-- created on 2026-10-05
