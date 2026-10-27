import Mathlib
import Initialize.Tactic.Attr.Basic
open Topology Set
open scoped TensorProduct


/--
[closedEmbedding_prodMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma closedEmbedding_prodMap
  [TopologicalSpace X₁]
  [TopologicalSpace Y₁]
  [TopologicalSpace X₂]
  [TopologicalSpace Y₂]
  {f : X₁ → Y₁}
  {g : X₂ → Y₂}
-- given
  (hf : IsClosedEmbedding f)
  (hg : IsClosedEmbedding g) :
-- imply
  IsClosedEmbedding (Prod.map f g) where toIsEmbedding :=
-- proof
  hf.toIsEmbedding.prodMap hg.toIsEmbedding
    isClosed_range := by
      rw [Set.range_prodMap]
      exact hf.isClosed_range.prod hg.isClosed_range

/--
[isClosed_prod_of_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma isClosed_prod_of_isClosed
  [TopologicalSpace Y₁]
  [TopologicalSpace Y₂]
  {S₁ : Set Y₁}
  {S₂ : Set Y₂}
-- given
  (h₁ : IsClosed S₁)
  (h₂ : IsClosed S₂) :
-- imply
  IsClosed (S₁ ×ˢ S₂) :=
-- proof
  h₁.prod h₂

/--
[tensorProduct_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma tensorProduct_map_surjective
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [AddCommMonoid N]
  [Module R N]
  [AddCommMonoid M']
  [Module R M']
  [AddCommMonoid N']
  [Module R N']
  {f : M →ₗ[R] M'}
  {g : N →ₗ[R] N'}
-- given
  (hf : Function.Surjective f)
  (hg : Function.Surjective g) :
-- imply
  Function.Surjective (TensorProduct.map f g) :=
-- proof
  TensorProduct.map_surjective hf hg

/--
[algHom_tensorProduct_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma algHom_tensorProduct_map_surjective
  [CommSemiring R]
  [CommSemiring A₁]
  [CommSemiring B₁]
  [CommSemiring A₂]
  [CommSemiring B₂]
  [Algebra R A₁]
  [Algebra R B₁]
  [Algebra R A₂]
  [Algebra R B₂]
  {φ : A₁ →ₐ[R] B₁}
  {ψ : A₂ →ₐ[R] B₂}
-- given
  (hφ : Function.Surjective φ)
  (hψ : Function.Surjective ψ) :
-- imply
  Function.Surjective (Algebra.TensorProduct.map φ ψ) :=
-- proof
  TensorProduct.map_surjective hφ hψ

/--
[ringHom_eq_of_crossRatio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma ringHom_eq_of_crossRatio
  [CommRing A]
  [CommRing B]
  [NoZeroDivisors B]
  {f g : A →+* B}
  {s : A}
-- given
  (hgs : g s ≠ 0)
  (h : ∀ a : A, f a * g s = g a * f s) :
-- imply
  f = g := by
-- proof
  have hs_eq : f s = g s := by
    have h1 := h 1; simp at h1; exact h1.symm
  ext a
  rw [hs_eq] at h
  exact mul_right_cancel₀ hgs (h a)

/--
[ringHom_eq_of_eq_on_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma ringHom_eq_of_eq_on_base
  [CommSemiring R]
  {M : Submonoid R}
  [CommSemiring S]
  [Algebra R S]
  [IsLocalization M S]
  [Semiring P]
  {j k : S →+* P}
-- given
  (h : ∀ a : R, j (algebraMap R S a) = k (algebraMap R S a)) :
-- imply
  j = k :=
-- proof
  IsLocalization.ringHom_ext M (RingHom.ext h)

/--
[fieldHom_eq_of_eq_on_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProductsSeparatedness.lean)
-/
@[path]
lemma fieldHom_eq_of_eq_on_domain
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  {f g : K →+* L}
-- given
  (h : ∀ a : A, f (algebraMap A K a) = g (algebraMap A K a)) :
-- imply
  f = g :=
-- proof
  IsFractionRing.ringHom_ext h


-- created on 2026-10-23
