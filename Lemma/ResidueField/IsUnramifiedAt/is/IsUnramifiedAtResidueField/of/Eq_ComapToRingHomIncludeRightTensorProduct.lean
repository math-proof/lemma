import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


private lemma isUnramifiedAt_iff_subsingleton
  [CommRing S] [CommRing B] [Algebra S B] [Algebra.EssFiniteType S B]
  (q : Ideal B) [q.IsPrime] :
-- imply
  Algebra.IsUnramifiedAt S q ↔ Subsingleton (q.ResidueField ⊗[B] Ω[B⁄S]) := by
-- proof
  have h : Algebra.IsUnramifiedAt S q ↔
      (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus S B := Iff.rfl
  rw [h, Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]


/--
[Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
  {P : Ideal R} [P.IsPrime]
  {Q : Ideal A} [Q.IsPrime] [Q.LiesOver P]
  {Q' : Ideal (P.Fiber A)} [Q'.IsPrime]
-- given
  (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
-- imply
  Algebra.IsUnramifiedAt R Q ↔ Algebra.IsUnramifiedAt P.ResidueField Q' := by
-- proof
  let _ : Algebra A (P.Fiber A) := Algebra.TensorProduct.rightAlgebra
  rw [isUnramifiedAt_iff_subsingleton (S := R) (B := A) Q,
    isUnramifiedAt_iff_subsingleton (S := P.ResidueField) (B := P.Fiber A) Q']
  let e1 : P.Fiber A ⊗[A] Ω[A⁄R] ≃ₗ[P.Fiber A] Ω[P.Fiber A⁄P.ResidueField] :=
    KaehlerDifferential.tensorKaehlerEquiv R P.ResidueField A (P.Fiber A)
  let e2 : Q'.ResidueField ⊗[P.Fiber A] Ω[P.Fiber A⁄P.ResidueField] ≃ₗ[Q'.ResidueField]
    Q'.ResidueField ⊗[A] Ω[A⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q'.ResidueField Q'.ResidueField)
      e1.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (P.Fiber A) Q'.ResidueField
        Q'.ResidueField Ω[A⁄R])
  have hQ'' : Q = Q'.comap (Algebra.ofId A (P.Fiber A)).toRingHom := hQ'
  let g : Q.ResidueField →ₐ[A] Q'.ResidueField :=
    Ideal.ResidueField.mapₐ Q Q' (Algebra.ofId A (P.Fiber A)) hQ''
  let _ : Algebra Q.ResidueField Q'.ResidueField := g.toRingHom.toAlgebra
  have : IsScalarTower A Q.ResidueField Q'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  let e3 : Q'.ResidueField ⊗[A] Ω[A⁄R] ≃ₗ[Q'.ResidueField]
    Q'.ResidueField ⊗[Q.ResidueField] (Q.ResidueField ⊗[A] Ω[A⁄R]) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Q.ResidueField Q'.ResidueField
      Q'.ResidueField Ω[A⁄R]).symm
  rw [(e2.trans e3).toEquiv.subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right Q.ResidueField Q'.ResidueField]


-- created on 2026-10-13
