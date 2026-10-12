import Mathlib
import Lemma.Int.FormallyEtale.of.Bijective
import sympy.Basic
open Int KaehlerDifferential
open scoped TensorProduct


/--
[Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential.lean)
-/
@[path]
private lemma main
  {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
  {ι : Type u} [Finite ι]
  {a : ι → A} {b : Module.Basis ι A (Ω[A⁄R])}
-- given
  (hb : ∀ i, b i = D R A (a i)) :
-- imply
  (MvPolynomial.aeval a : MvPolynomial ι R →ₐ[R] A).toRingHom.Etale := by
-- proof
  classical
  let _ : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval a).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval a).commutes r).symm
  have halg : ∀ p : MvPolynomial ι R, algebraMap (MvPolynomial ι R) A p = MvPolynomial.aeval a p :=
    fun _ => rfl
  let b' : Module.Basis ι A (A ⊗[MvPolynomial ι R] Ω[(MvPolynomial ι R)⁄R]) :=
    Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hX : ∀ i, mvPolynomialBasis R ι i = D R (MvPolynomial ι R) (MvPolynomial.X i) :=
    fun i => Module.Basis.apply_eq_iff.mpr (mvPolynomialBasis_repr_D_X R ι i)
  have hb' : ∀ i, mapBaseChange R (MvPolynomial ι R) A (b' i) = b i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, mapBaseChange_tmul, one_smul, hX, map_D, halg,
      MvPolynomial.aeval_X, hb]
  have heq : mapBaseChange R (MvPolynomial ι R) A = (b'.equiv b (Equiv.refl ι)).toLinearMap :=
    b'.ext fun i => by rw [hb', LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [heq]
    apply (b'.equiv b (Equiv.refl ι)).bijective
  have : Algebra.FormallyEtale (MvPolynomial ι R) A := FormallyEtale.of.Bijective hbij
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.Etale (MvPolynomial ι R) A := ⟨inferInstance, inferInstance⟩
  apply RingHom.etale_algebraMap.mpr this


-- created on 2026-10-12
