import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {k : Type u} [Field k]
variable {A : Type u} [CommRing A] [Bialgebra k A]
variable {C : Type u} [CommRing C] [Bialgebra k C]

private noncomputable def prodBialgHom (ρ₀ ρ₁ : BialgHom k A C) : BialgHom k (TensorProduct k A A) C :=
  (Bialgebra.mulBialgHom k C).comp (Bialgebra.TensorProduct.map ρ₀ ρ₁)

private lemma prodBialgHom_apply (ρ₀ ρ₁ : BialgHom k A C) (x : TensorProduct k A A) :
  -- imply
  prodBialgHom ρ₀ ρ₁ x = Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C) x := by
  -- proof
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change Bialgebra.mulBialgHom k C (Bialgebra.TensorProduct.map ρ₀ ρ₁ (TensorProduct.tmul k a b)) = _
    rw [Bialgebra.TensorProduct.map_tmul]
    apply Algebra.TensorProduct.lmul'_apply_tmul (R := k) (ρ₀ a) (ρ₁ b)
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

/--
[Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq.lean)
-/
@[path]
private lemma main
  (k : Type u) [Field k]
  (A : Type u) [CommRing A] [Bialgebra k A]
  (C : Type u) [CommRing C] [Bialgebra k C]
  [FiniteDimensional k A] [FiniteDimensional k C]
  (ρ₀ ρ₁ : BialgHom k A C)
  (hsurj : Function.Surjective (Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C)))
  (hrank : Module.finrank k C = Module.finrank k A * Module.finrank k A) :
  -- imply
  ∃ κ : BialgEquiv k C (TensorProduct k A A), (∀ a : A, κ.symm (TensorProduct.tmul k a 1) = ρ₀ a) ∧ (∀ a : A, κ.symm (TensorProduct.tmul k 1 a) = ρ₁ a) ∧ ∀ x : TensorProduct k A A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C) x := by
  -- proof
  classical
  let π : BialgHom k (TensorProduct k A A) C := prodBialgHom ρ₀ ρ₁
  have hπ : ∀ x, π x = Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C) x := prodBialgHom_apply ρ₀ ρ₁
  have hπsurj : Function.Surjective π := by
    intro c
    obtain ⟨x, rfl⟩ := hsurj c
    refine ⟨x, hπ x⟩
  have hdim : Module.finrank k (TensorProduct k A A) = Module.finrank k C := by
    rw [Module.finrank_tensorProduct, hrank]
  have hπinj : Function.Injective π := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := π.toLinearMap)).2 hπsurj
  refine ⟨(BialgEquiv.ofBijective π ⟨hπinj, hπsurj⟩).symm, fun a => ?_, fun a => ?_, fun x => ?_⟩
  ·
    change π (TensorProduct.tmul k a 1) = ρ₀ a
    rw [hπ, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  ·
    change π (TensorProduct.tmul k 1 a) = ρ₁ a
    rw [hπ, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl
  ·
    change π x = Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C) x
    apply hπ x


-- created on 2026-10-20
