import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Homogeneous element of an augmentation-ideal multiple lies in the graded span of positive-degree products
(atlas homog_in_aug_smul).

[homog_in_aug_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
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
  {ℳ : ℕ → Submodule k M}
  {d : ℕ}
  {x : M}
-- given
  (hinter : DirectSum.IsInternal ℳ)
  (hsmul : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hxd : x ∈ ℳ d)
  (hxP : x ∈ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)) :
-- imply
  x ∈ Submodule.span k (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
    Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M)) := by
-- proof
  classical
  have : DirectSum.Decomposition ℳ := hinter.chooseDecomposition
  set target := Submodule.span k
    (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
      Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M))
  have hx_eq : (↑((DirectSum.decompose ℳ x) d) : M) = x :=
    DirectSum.decompose_of_mem_same ℳ hxd
  rw [← hx_eq]
  clear hxd hx_eq
  refine Submodule.smul_induction_on hxP ?_ ?_
  ·
    intro r hr n _
    suffices key : ∀ (r : S), r ∈ Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S)) → ∀ (n : M),
      (↑((DirectSum.decompose ℳ (r • n)) d) : M) ∈ target from key r hr n
    intro r hr
    induction hr using Submodule.span_induction with
    | mem s hs =>
      intro n
      simp only [Set.mem_iUnion] at hs
      obtain ⟨j, hj, hs_j⟩ := hs
      rw [(DirectSum.sum_support_decompose ℳ n).symm, Finset.smul_sum,
        DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
      apply Submodule.sum_mem
      intro i _
      have hni_mem := SetLike.coe_mem ((DirectSum.decompose ℳ n) i)
      have hsmul_mem : s • (↑((DirectSum.decompose ℳ n) i) : M) ∈ ℳ (i + j) :=
        hsmul i j s _ hs_j hni_mem
      if he : d = i + j then
        subst he
        rw [DirectSum.decompose_of_mem_same ℳ hsmul_mem]
        apply Submodule.subset_span
        simp only [Set.mem_iUnion]
        exact ⟨j, hj, i, rfl, Set.mem_image2_of_mem hs_j (SetLike.coe_mem _)⟩
      else
        simp [DirectSum.decompose_of_mem_ne ℳ hsmul_mem (Ne.symm he)]
    | zero =>
      intro n
      simp only [zero_smul, DirectSum.decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero]
      exact target.zero_mem
    | add _ _ _ _ ih₁ ih₂ =>
      intro n
      rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      exact target.add_mem (ih₁ n) (ih₂ n)
    | smul a _ _ ih =>
      intro n
      change (↑((DirectSum.decompose ℳ ((a * _) • n)) d) : M) ∈ target
      rw [mul_comm, mul_smul]
      exact ih (a • n)
  ·
    intro x y hx hy
    rw [DirectSum.decompose_add]
    simp only [DirectSum.add_apply, AddMemClass.coe_add]
    exact target.add_mem hx hy


-- created on 2026-10-24
