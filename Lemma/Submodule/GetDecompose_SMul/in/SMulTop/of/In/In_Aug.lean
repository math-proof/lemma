import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Graded component of a homogeneous augmentation-ideal scalar multiple stays in the augmentation-ideal multiple
(atlas homog_smul_component_mem_aug).

[homog_smul_component_mem_aug](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  [CommRing S]
  [Algebra k S]
  [AddCommGroup M]
  [Module S M]
  [Module k M]
  [IsScalarTower k S M]
  {𝒮 : ℕ → Submodule k S} [GradedAlgebra 𝒮]
  {ℳ : ℕ → Submodule k M} [DirectSum.Decomposition ℳ]
  {d j : ℕ}
  {rj : S}
  {n : M}
-- given
  (hsmul : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hrj_homog : rj ∈ 𝒮 j)
  (hrj_aug : rj ∈ Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) :
-- imply
  ((DirectSum.decompose ℳ (rj • n)) d : M) ∈ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S)) : Ideal S) • (⊤ : Submodule S M) := by
-- proof
  classical
  have h_eq : ((DirectSum.decompose ℳ (rj • n)) d : M) =
    ∑ i ∈ (DirectSum.decompose ℳ n).support,
      ((DirectSum.decompose ℳ (rj • ((DirectSum.decompose ℳ n) i : M))) d : M) := by
    conv_lhs => rw [show rj • n = ∑ i ∈ (DirectSum.decompose ℳ n).support,
      rj • ((DirectSum.decompose ℳ n) i : M) by
      conv_lhs => rw [← DirectSum.sum_support_decompose ℳ n]; rw [Finset.smul_sum]]
    rw [DirectSum.decompose_sum]; simp
  rw [h_eq]
  apply Submodule.sum_mem
  intro i _
  have h_mem_grade := hsmul i j rj _ hrj_homog ((DirectSum.decompose ℳ n) i).2
  if h : i + j = d then
    rw [← h, DirectSum.decompose_of_mem_same ℳ h_mem_grade]
    exact Submodule.smul_mem_smul hrj_aug Submodule.mem_top
  else
    rw [DirectSum.decompose_of_mem_ne ℳ h_mem_grade h]; exact Submodule.zero_mem _


-- created on 2026-10-24
