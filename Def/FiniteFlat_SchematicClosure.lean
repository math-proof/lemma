import Mathlib
import Instance.FiniteFlat_SchematicClosure

open scoped TensorProduct

section FlatClosure

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G] [Algebra R G]


def flatClosure (B : Subalgebra F (F ⊗[R] G)) : Subalgebra R G where
  carrier := {g : G | (1 : F) ⊗ₜ[R] g ∈ B}
  mul_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) * ((1 : F) ⊗ₜ[R] b) ∈ B := mul_mem ha hb
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
    exact h
  one_mem' := by
    show (1 : F) ⊗ₜ[R] (1 : G) ∈ B
    rw [← Algebra.TensorProduct.one_def]
    exact one_mem B
  add_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) + ((1 : F) ⊗ₜ[R] b) ∈ B := add_mem ha hb
    rw [← TensorProduct.tmul_add] at h
    exact h
  zero_mem' := by
    show (1 : F) ⊗ₜ[R] (0 : G) ∈ B
    rw [TensorProduct.tmul_zero]
    exact zero_mem B
  algebraMap_mem' r := by
    show (1 : F) ⊗ₜ[R] (algebraMap R G r) ∈ B
    have h1 : (1 : F) ⊗ₜ[R] (algebraMap R G r) = (algebraMap R F r) ⊗ₜ[R] (1 : G) := by
      rw [Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        ← Algebra.algebraMap_eq_smul_one]
    rw [h1, ← Algebra.TensorProduct.algebraMap_apply]
    exact B.algebraMap_mem _

end FlatClosure
