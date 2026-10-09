import Mathlib
import sympy.Basic

open scoped Pointwise

/--
[closure_eq_iUnion_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Group/Subgroup/Pointwise.lean)
-/
@[path]
private lemma main
  [Group G]
  {X : Set G}
-- given
  (hX : X⁻¹ = X) :
-- imply
  (Subgroup.closure X : Set G) = ⋃ n : ℕ, X ^ n := by
-- proof
  have hUnion : X ∪ X⁻¹ = X := by
    rw [hX, Set.union_self]
  have hSubmonoid : (Subgroup.closure X).toSubmonoid = Submonoid.closure X := calc
    _ = Submonoid.closure (X ∪ X⁻¹) := Subgroup.closure_toSubmonoid X
    _ = Submonoid.closure X := by rw [hUnion]
  have h_eq : (Submonoid.closure X : Set G) = ⋃ n : ℕ, X ^ n := by
    rw [Submonoid.closure_eq_image_prod]
    apply Set.eq_of_subset_of_subset
    ·
      intro x hx
      simp only [Set.mem_image, Set.mem_ofPred_eq] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      induction l with
      | nil =>
        exact Set.mem_iUnion.mpr ⟨0, by simp⟩
      | cons hd tl ih =>
        have hhd : hd ∈ X := hl hd (by simp)
        have htl : ∀ y ∈ tl, y ∈ X := fun y hy => hl y (List.mem_cons_of_mem hd hy)
        have hmem_tl : List.prod tl ∈ (⋃ n : ℕ, X ^ n) := ih htl
        obtain ⟨n, hn⟩ : ∃ n : ℕ, List.prod tl ∈ (X ^ n) := Set.mem_iUnion.mp hmem_tl
        exact Set.mem_iUnion.mpr ⟨n + 1, (pow_succ' X n).symm ▸ Set.mul_mem_mul hhd hn⟩
    ·
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      induction n generalizing x with
      | zero =>
        have hx1 : x = 1 := by
          simpa [Set.mem_singleton_iff] using hn
        subst hx1
        exact ⟨[], by simp, by simp⟩
      | succ n ih =>
        have hpow : X ^ (n + 1) = X * (X ^ n) :=
          pow_succ' X n
        have hx_mul : x ∈ X * (X ^ n) := hpow ▸ hn
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx_mul
        obtain ⟨l, hl, rfl⟩ := ih hb
        exact ⟨a :: l, by
          intro y hy
          simp only [List.mem_cons] at hy
          obtain rfl | hy := hy
          · exact ha
          · exact hl y hy, by simp⟩
  calc
    _ = ((Subgroup.closure X).toSubmonoid : Set G) := rfl
    _ = (Submonoid.closure X : Set G) := by rw [hSubmonoid]
    _ = ⋃ n : ℕ, X ^ n := h_eq


-- created on 2026-10-09
