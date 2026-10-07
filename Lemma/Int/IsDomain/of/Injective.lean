import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_TensorProduct_isDomain_of_injective_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_isDomain_of_injective_of_flat.lean)
-/
@[main]
private lemma main
  {R k A K : Type*} [CommRing R] [CommRing k] [Algebra R k] [Module.Flat R k] [CommRing A] [Algebra R A] [CommRing K] [Algebra R K] [IsDomain (k ⊗[R] K)]
  {f : A →ₐ[R] K}
-- given
  (hf : Function.Injective f) :
-- imply
  IsDomain (k ⊗[R] A) := by
-- proof
  let g : k ⊗[R] A →ₐ[k] k ⊗[R] K := Algebra.TensorProduct.map (AlgHom.id k k) f
  have hg : Function.Injective g := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := k) f.toLinearMap hf
    intro x y hxy
    apply h
    simp [g] at hxy
    exact hxy

  have : Nontrivial (k ⊗[R] A) := g.toRingHom.domain_nontrivial
  exact hg.isDomain g.toRingHom


-- created on 2026-10-05
