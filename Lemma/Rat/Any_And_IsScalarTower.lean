import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {R W k : Type} [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] [Field k] [IsAlgClosed k] [Algebra R k] :
-- imply
  ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (_ : Algebra R k') (_ : Algebra W k') (_ : Algebra k k'),
      IsScalarTower R W k' ∧ IsScalarTower R k k' := by
-- proof
  classical
  have : Nontrivial (k ⊗[R] W) := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (k ⊗[R] W)
  have := h𝔪
  let : Field ((k ⊗[R] W) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨π⟩ : Nonempty (k ⊗[R] W →+* AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
    ⟨(algebraMap ((k ⊗[R] W) ⧸ 𝔪) (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪))).comp (Ideal.Quotient.mk 𝔪)⟩
  refine ⟨AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪), inferInstance, inferInstance,
    (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra, ?_, ?_⟩
  · let : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    let : Algebra W (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeRight (algebraMap R W r))
      rw [AlgHom.commutes])
  · let : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    let : Algebra k (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeLeftRingHom (algebraMap R k r))
      rfl)


-- created on 2026-10-05
