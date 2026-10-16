import Mathlib
import sympy.Basic
open scoped TensorProduct


private lemma rTensor_comp_map
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A]
  {D : Type u} [CommRing D] [Algebra R D]
  {C : Type u} [CommRing C] [Algebra R C]
  {φ : D →ₐ[R] C} {T : Subalgebra R A} {w : ↥T ⊗[R] D} :
-- imply
  (LinearMap.rTensor C T.val.toLinearMap) (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ w) =
    Algebra.TensorProduct.map (AlgHom.id A A) φ (LinearMap.rTensor D T.val.toLinearMap w) := by
-- proof
  induction w using TensorProduct.inductionOn with
  | tmul t d =>
    simp
  | add x y hx hy =>
    simp [map_add, hx, hy]


private lemma rTensor_incl_map
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A]
  {D : Type u} [CommRing D] [Algebra R D]
  {C : Type u} [CommRing C] [Algebra R C]
  {φ : D →ₐ[R] C} {T T' : Subalgebra R A} {w : ↥T ⊗[R] D}
-- given
  (h : T ≤ T') :
-- imply
  (LinearMap.rTensor C (Subalgebra.inclusion h).toLinearMap)
    (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ w) =
    Algebra.TensorProduct.map (AlgHom.id ↥T' ↥T') φ
      (LinearMap.rTensor D (Subalgebra.inclusion h).toLinearMap w) := by
-- proof
  induction w using TensorProduct.inductionOn with
  | tmul t d =>
    simp
  | add x y hx hy =>
    simp [map_add, hx, hy]


private lemma step
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A]
  {D : Type u} [CommRing D] [Algebra R D]
  {C : Type u} [CommRing C] [Algebra R C]
  {φ : D →ₐ[R] C} {T₀ : Subalgebra R A} {c : C}
-- given
  (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ))
  (hT₀ : T₀.FG) :
-- imply
  ∃ (T : Subalgebra R A) (_ : T₀ ≤ T), T.FG ∧
    (1 : ↥T) ⊗ₜ[R] c ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
-- proof
  classical
  obtain ⟨w, hw⟩ := hA ((1 : A) ⊗ₜ[R] c)
  obtain ⟨T₁, hT₁, ⟨w₁, hw₁⟩⟩ := TensorProduct.Algebra.exists_of_fg w
  let T₂ := T₀ ⊔ T₁
  have hT₂ : T₂.FG := hT₀.sup hT₁
  let w₂ : ↥T₂ ⊗[R] D :=
    LinearMap.rTensor D (Subalgebra.inclusion (le_sup_right : T₁ ≤ T₂)).toLinearMap w₁
  have heq : LinearMap.rTensor C T₂.val.toLinearMap (Algebra.TensorProduct.map (AlgHom.id ↥T₂ ↥T₂) φ w₂) =
      LinearMap.rTensor C T₂.val.toLinearMap ((1 : ↥T₂) ⊗ₜ[R] c) := by
    rw [rTensor_comp_map]
    have : LinearMap.rTensor D T₂.val.toLinearMap w₂ = w := by
      rw [← hw₁]
      show (LinearMap.rTensor D T₂.val.toLinearMap) ((LinearMap.rTensor D _) w₁) = _
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      rfl
    rw [this, hw]
    simp
  obtain ⟨T, hT₂T, hT, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hT₂ heq
  refine ⟨T, le_sup_left.trans hT₂T, hT, ⟨LinearMap.rTensor D (Subalgebra.inclusion hT₂T).toLinearMap w₂, ?_⟩⟩
  rw [← rTensor_incl_map, h]
  simp


/--
[Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A]
  {D : Type u} [CommRing D] [Algebra R D]
  {C : Type u} [CommRing C] [Algebra R C]
  {φ : D →ₐ[R] C} {s : Finset A}
-- given
  (hφ : φ.toRingHom.FiniteType)
  (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ)) :
-- imply
  ∃ (T : Subalgebra R A), T.FG ∧ (↑s : Set A) ⊆ T ∧
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
-- proof
  classical
  let _ : Algebra D C := φ.toRingHom.toAlgebra
  have hft : Algebra.FiniteType D C := hφ
  obtain ⟨gens, hgens⟩ := hft.out
  have key : ∀ (l : List C), ∃ (T : Subalgebra R A), Algebra.adjoin R (↑s : Set A) ≤ T ∧ T.FG ∧
      ∀ c ∈ l, (1 : ↥T) ⊗ₜ[R] c ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
    intro l
    induction l with
    | nil =>
      refine ⟨Algebra.adjoin R (↑s : Set A), le_rfl, Subalgebra.fg_adjoin_finset _, fun c hc => ?_⟩
      simp at hc
    | cons c l ih =>
      obtain ⟨T₀, hsT₀, hT₀, hl⟩ := ih
      obtain ⟨T, hT₀T, hT, hc⟩ := step hA hT₀
      refine ⟨T, hsT₀.trans hT₀T, hT, fun c' hc' => ?_⟩
      obtain rfl | hmem := List.mem_cons.mp hc'
      · apply hc
      ·
        obtain ⟨w, hw⟩ := hl c' hmem
        refine ⟨LinearMap.rTensor D (Subalgebra.inclusion hT₀T).toLinearMap w, ?_⟩
        rw [← rTensor_incl_map, hw]
        simp
  obtain ⟨T, hsT, hT, hgen⟩ := key gens.toList
  refine ⟨T, hT, fun a ha => hsT (Algebra.subset_adjoin ha), ?_⟩
  let ψ := Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ
  have h1c : ∀ c : C, (1 : ↥T) ⊗ₜ[R] c ∈ Set.range ψ := by
    intro c
    have hc : c ∈ Algebra.adjoin D (↑gens : Set C) := by
      rw [hgens]
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      apply hgen x (Finset.mem_toList.mpr hx)
    | algebraMap d =>
      refine ⟨(1 : ↥T) ⊗ₜ[R] d, ?_⟩
      simp [ψ]
      rfl
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb, TensorProduct.tmul_add]
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul t c =>
    obtain ⟨a, ha⟩ := h1c c
    refine ⟨(t ⊗ₜ[R] (1 : D)) * a, ?_⟩
    rw [map_mul, ha]
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb]


-- created on 2026-10-16
