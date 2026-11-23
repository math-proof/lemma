module

public import Mathlib
public import Def.DedekindDomain_FiniteAdeleRing_TensorPi
public import Class.Mathlib_Algebra_IsDirectLimit
public import Theorem.Set.Algebra.RestrictedProduct.Basic
public import Instance.DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted

@[expose] public section

section

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

def rangeLTensor (i : ι) : Submodule R (M ⊗[R] N i) :=
  LinearMap.range (LinearMap.lTensor M ((L i).subtype))

noncomputable def rangeLTensorLeft (R M : Type*) [CommSemiring R] [CommSemiring M] [Algebra R M]
    {ι : Type*} (N : ι → Type*) [∀ i, Semiring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (i : ι) : Submodule M (M ⊗[R] N i) :=
  (TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype).range

set_option backward.isDefEq.respectTransparency false in

def lTensor :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensor R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  TensorProduct.lift {
    toFun m := mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id
        (fun i ↦ TensorProduct.mk R M (N i) m) (hmap m)
    map_add' m n := by ext; simp
    map_smul' a m := by ext; simp
  }

noncomputable def lTensorLeft (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (ℱ : Filter ι)
    (L : ∀ i, Submodule R (N i)) :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensorLeft R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  let f : (i : ι) → N i →ₗ[R] M ⊗[R] N i := fun i ↦
    { toFun n := 1 ⊗ₜ n, map_add' _ _ := by simp [tmul_add], map_smul' := by simp }
  have (i : ι) : SMulMemClass (Submodule M (M ⊗[R] N i)) R ((fun x ↦ M ⊗[R] N x) i) :=
    .ofIsScalarTower _ _ _ _
  have : IsScalarTower R M Πʳ (i : ι), [M ⊗[R] N i, ↑(rangeLTensorLeft R M N L i)]_[ℱ] := by
    apply IsScalarTower.mk fun r m x ↦ by ext; simp
  (mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id f (hmap 1)).liftBaseChange _

variable (S : Set ι) [Module.FinitePresentation R M] [Module.Flat R M]

noncomputable def tmulEquivRangeLTensor (i : ι) : M ⊗[R] (L i) ≃ₗ[R] rangeLTensor R M N L i :=
  LinearEquiv.ofInjective (LinearMap.lTensor M (Submodule.subtype <| L i))
    (Module.Flat.lTensor_preserves_injective_linearMap (L i).subtype
      (Submodule.injective_subtype (L i)))

open scoped Filter in

noncomputable def lTensorPrincipalEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] :=
  let N' (i : ι) := if i ∈ S then L i else (⊤ : Submodule R (N i))
  let f : Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] (Π i, N' i) := {
    toFun x i := ⟨x i, by
      by_cases h : i ∈ S
      · have hx := x.property h; simp [N', h] at hx ⊢; exact hx
      · simp [N', h]⟩
    invFun x := ⟨fun i ↦ x i, by
      rw [Filter.eventually_principal]
      intro y hy
      have hp := (x y).prop; simp only [N', hy, ↓reduceIte] at hp ⊢; exact hp⟩
    map_add' x y := by ext; simp
    map_smul' a x := by ext; simp
  }
  let g1 : M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] M ⊗[R] (Π i, N' i) := LinearEquiv.lTensor M f
  let g2 : M ⊗[R] (Π i, N' i) ≃ₗ[R] Π i, M ⊗[R] N' i :=
    tensorPi_equiv_piTensor' R M fun i ↦ ↥(N' i)
  let gEquiv (i : ι) (h : i ∈ S) : M ⊗[R] (N' i) ≃ₗ[R] rangeLTensor R M N L i :=
    (LinearEquiv.lTensor M (LinearEquiv.ofEq _ _ (by simp [N', h]))) ≪≫ₗ
      (tmulEquivRangeLTensor R M N L i)
  let gEquiv' (i : ι) (h : i ∉ S) : M ⊗[R] (N' i) ≃ₗ[R] M ⊗[R] N i :=
    LinearEquiv.lTensor M <| LinearEquiv.ofTop (N' i) (by simp [N', h])
  let g3 : (Π i, M ⊗[R] N' i) ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] := {
    toFun x := ⟨
      fun i ↦ if h : i ∈ S then gEquiv i h (x i) else gEquiv' i h (x i),
      by
        rw [Filter.eventually_principal]
        intro i h
        simp [h]⟩
    invFun x i := if h : i ∈ S then
        gEquiv i h |>.symm ⟨(x i), by have hx := x.property h; simp at hx ⊢; exact hx⟩
      else
        gEquiv' i h |>.symm (x i)
    left_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    right_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_add' x y := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_smul' a x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
  }
  g1 ≪≫ₗ g2 ≪≫ₗ g3

set_option backward.isDefEq.respectTransparency false in
open scoped Filter in
set_option backward.isDefEq.respectTransparency false in
open scoped Filter in
noncomputable def lTensorEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L) (lTensor_bijective R M N ℱ L)

noncomputable def lTensorEquivLeft (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensorLeft R M N ℱ L) (lTensorLeft_bijective R M N L ℱ)

end RestrictedProduct

end

end
