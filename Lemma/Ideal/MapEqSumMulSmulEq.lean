import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def g
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  (γ : Γ) :
  (S ⊗[W] W') →ₐ[S] S ⊗[W] W' :=
  Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)

private noncomputable def Tr
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  (m : S ⊗[W] W') :
  S ⊗[W] W' :=
  ∑ γ : Γ, g γ m

private lemma g_tmul
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {γ : Γ}
  {a : S}
  {w : W'} :
  g γ (a ⊗ₜ[W] w) = a ⊗ₜ[W] (γ • w) := by
  simp [g, Algebra.TensorProduct.map_tmul]

private lemma Tr_add
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {m₁ m₂ : S ⊗[W] W'} :
  Tr (Γ := Γ) (m₁ + m₂) = Tr (Γ := Γ) m₁ + Tr (Γ := Γ) m₂ := by
  simp [Tr, map_add, Finset.sum_add_distrib]

private lemma Tr_zero
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S] :
  Tr (Γ := Γ) (0 : S ⊗[W] W') = 0 := by
  simp [Tr]

private lemma Tr_tmul
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {a : S}
  {w : W'} :
  Tr (Γ := Γ) (a ⊗ₜ[W] w) = a ⊗ₜ[W] (∑ γ : Γ, γ • w) := by
  simp [Tr, g_tmul, TensorProduct.tmul_sum]

private lemma smul_sum_smul
  [CommRing W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W']
  {δ : Γ}
  {w : W'} :
  δ • (∑ γ : Γ, γ • w) = ∑ γ : Γ, γ • w := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft δ) (fun γ => γ • w)

private lemma Tr_mem_range
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {m : S ⊗[W] W'}
  -- given
  (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W')) :
  -- imply
  ∃ s : S, Tr (Γ := Γ) m = (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') s := by
  -- proof
  refine TensorProduct.inductionOn m ?_ ?_
  ·
    intro a w
    obtain ⟨c, hc⟩ := hinv (∑ γ : Γ, γ • w) (fun δ => smul_sum_smul (δ := δ) (w := w))
    refine ⟨c • a, ?_⟩
    rw [Tr_tmul, ← hc, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]
  ·
    intro m₁ m₂ h₁ h₂
    obtain ⟨s₁, hs₁⟩ := h₁
    obtain ⟨s₂, hs₂⟩ := h₂
    exact ⟨s₁ + s₂, by rw [Tr_add, hs₁, hs₂, map_add]⟩

private lemma g_one
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {m : S ⊗[W] W'} :
  g (1 : Γ) m = m := by
  refine TensorProduct.inductionOn m ?_ ?_
  ·
    intro a w
    rw [g_tmul, one_smul]
  ·
    intro m₁ m₂ h₁ h₂
    rw [map_add, h₁, h₂]

private lemma eq_sum_mul_Tr
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {n : ℕ}
  {x y : Fin n → W'}
  {m : S ⊗[W] W'}
  -- given
  (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0) :
  -- imply
  m = ∑ i, ((1 : S) ⊗ₜ[W] x i) * Tr (Γ := Γ) (((1 : S) ⊗ₜ[W] y i) * m) := by
  -- proof
  have key : ∀ γ : Γ, ∑ i, ((1 : S) ⊗ₜ[W] x i) * g γ (((1 : S) ⊗ₜ[W] y i) * m) = (if γ = 1 then 1 else 0 : S ⊗[W] W') * g γ m := by
    intro γ
    have h1 : ∀ i, ((1 : S) ⊗ₜ[W] x i) * g γ (((1 : S) ⊗ₜ[W] y i) * m) = ((1 : S) ⊗ₜ[W] (x i * γ • y i)) * g γ m := by
      intro i
      rw [map_mul, g_tmul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp_rw [h1]
    rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, hxy γ]
    split_ifs
    · rw [Algebra.TensorProduct.one_def]
    · rw [TensorProduct.tmul_zero]
  calc
    _ = g (1 : Γ) m := (g_one (m := m)).symm
    _ = ∑ γ : Γ, (if γ = 1 then 1 else 0 : S ⊗[W] W') * g γ m := by
      rw [Finset.sum_eq_single (1 : Γ)]
      · simp
      ·
        intro γ _ hγ
        simp [hγ]
      ·
        intro h
        apply absurd (Finset.mem_univ _) h
    _ = ∑ γ : Γ, ∑ i, ((1 : S) ⊗ₜ[W] x i) * g γ (((1 : S) ⊗ₜ[W] y i) * m) := by
      simp_rw [key]
    _ = ∑ i, ((1 : S) ⊗ₜ[W] x i) * Tr (Γ := Γ) (((1 : S) ⊗ₜ[W] y i) * m) := by
      rw [Finset.sum_comm]
      simp_rw [Tr, Finset.mul_sum]

/--
[Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq.lean)
-/
@[path]
private lemma main
  [CommRing W] [CommRing W'] [Algebra W W']
  [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  [CommRing S] [Algebra W S]
  {n : ℕ}
  {x y : Fin n → W'}
  {J' : Ideal (S ⊗[W] W')}
  -- given
  (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W'))
  (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0)
  (hstab : ∀ γ : Γ, J'.map (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) = J') :
  -- imply
  J' = (J'.comap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W')).map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') := by
  -- proof
  classical
  refine le_antisymm ?_ Ideal.map_comap_le
  intro m hm
  have hstab' : ∀ γ : Γ, ∀ m' ∈ J', g γ m' ∈ J' := by
    intro γ m' hm'
    have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) hm'
    rwa [hstab γ] at this
  rw [eq_sum_mul_Tr (m := m) (x := x) (y := y) hxy]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
  have hJ : Tr (Γ := Γ) (((1 : S) ⊗ₜ[W] y i) * m) ∈ J' := Ideal.sum_mem _ fun γ _ => hstab' γ _ (J'.mul_mem_left _ hm)
  obtain ⟨s, hs⟩ := Tr_mem_range (m := ((1 : S) ⊗ₜ[W] y i) * m) hinv
  rw [hs] at hJ ⊢
  apply Ideal.mem_map_of_mem _ (Iff.mpr Ideal.mem_comap hJ)


-- created on 2026-10-20
