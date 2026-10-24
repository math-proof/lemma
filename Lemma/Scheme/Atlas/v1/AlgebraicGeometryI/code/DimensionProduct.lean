import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DimensionProduct
open MvPolynomial


/--
[ringKrullDim_tensorProduct_mvPolynomial_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma ringKrullDim_tensorProduct_mvPolynomial_field
  {k : Type*}
  [Field k]
  {n m : ℕ} :
-- imply
  ringKrullDim (TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k)) = ↑n + ↑m := by
-- proof
  rw [dim_eq_of_ringEquiv (mvPolynomialTensorAlgEquiv k n m).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/--
[ringKrullDim_tensorProduct_mvPolynomial_eq_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma ringKrullDim_tensorProduct_mvPolynomial_eq_add
  {k : Type*}
  [Field k]
  {n m : ℕ} :
-- imply
  ringKrullDim (TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k)) = ringKrullDim (MvPolynomial (Fin n) k) + ringKrullDim (MvPolynomial (Fin m) k) := by
-- proof
  rw [ringKrullDim_tensorProduct_mvPolynomial_field,
    ringKrullDim_mvPolynomial_field, ringKrullDim_mvPolynomial_field]

/--
[ringKrullDim_eq_of_noetherNormalization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma ringKrullDim_eq_of_noetherNormalization
  [Field k]
  [CommRing R]
  [Algebra k R]
  {s : ℕ}
  {g : MvPolynomial (Fin s) k →ₐ[k] R}
-- given
  (hinj : Function.Injective g)
  (hfin : g.Finite) :
-- imply
  ringKrullDim R = ↑s := by
-- proof
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) R := hfin
  have : ringKrullDim R = ringKrullDim (MvPolynomial (Fin s) k) :=
    @FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite
      (MvPolynomial (Fin s) k) R _ _ g.toRingHom.toAlgebra ‹_› hinj
  rw [this, ringKrullDim_mvPolynomial_field]

/--
[ringKrullDim_fg_algebra_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma ringKrullDim_fg_algebra_eq_nat
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Nontrivial R]
  [Algebra k R]
  [Algebra.FiniteType k R] :
-- imply
  ∃ s : ℕ, ringKrullDim R = ↑s := by
-- proof
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  exact ⟨s, ringKrullDim_eq_of_noetherNormalization s g hinj hfin⟩

/--
[Algebra.TensorProduct.map_injective_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma Algebra.TensorProduct.map_injective_of_field
  [Field k]
  [CommRing A]
  [CommRing B]
  [CommRing C]
  [CommRing D]
  [Algebra k A]
  [Algebra k B]
  [Algebra k C]
  [Algebra k D]
  {f : A →ₐ[k] C}
  {g : B →ₐ[k] D}
-- given
  (hf : Function.Injective f)
  (hg : Function.Injective g) :
-- imply
  Function.Injective (Algebra.TensorProduct.map f g) := by
-- proof
  have := TensorProduct.map_injective_of_flat_flat
    (f.toLinearMap) (g.toLinearMap) hf hg
  intro x y hxy
  exact this hxy

/--
[ringKrullDim_tensorProduct_fg_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean)
-/
@[path]
lemma ringKrullDim_tensorProduct_fg_algebra
  {k : Type*}
  [Field k]
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra k A]
  [Algebra k B]
  [Algebra.FiniteType k A]
  [Algebra.FiniteType k B]
  [Nontrivial A]
  [Nontrivial B]
  [Nontrivial (TensorProduct k A B)] :
-- imply
  ringKrullDim (TensorProduct k A B) = ringKrullDim A + ringKrullDim B := by
-- proof
  obtain ⟨n, gA, hinjA, hfinA⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨m, gB, hinjB, hfinB⟩ := exists_finite_inj_algHom_of_fg k B
  have hdimA : ringKrullDim A = ↑n :=
    ringKrullDim_eq_of_noetherNormalization n gA hinjA hfinA
  have hdimB : ringKrullDim B = ↑m :=
    ringKrullDim_eq_of_noetherNormalization m gB hinjB hfinB
  let f := Algebra.TensorProduct.map gA gB
  have hf_inj : Function.Injective f :=
    Algebra.TensorProduct.map_injective_of_field gA gB hinjA hinjB
  let e := mvPolynomialTensorAlgEquiv k n m
  let g : MvPolynomial (Fin (n + m)) k →ₐ[k] TensorProduct k A B :=
    f.comp e.symm.toAlgHom
  have hg_inj : Function.Injective g := hf_inj.comp e.symm.injective
  have hg_fin : g.Finite := by
    have h1 : e.symm.toAlgHom.Finite :=
      AlgHom.Finite.of_surjective _ e.symm.surjective
    have h2 : f.Finite :=
      RingHom.Finite.tensorProductMap hfinA hfinB
    exact h2.comp h1
  have hdimAB : ringKrullDim (TensorProduct k A B) = ↑(n + m) :=
    ringKrullDim_eq_of_noetherNormalization (n + m) g hg_inj hg_fin
  rw [hdimAB, hdimA, hdimB]
  simp [Nat.cast_add]


-- created on 2026-10-23
