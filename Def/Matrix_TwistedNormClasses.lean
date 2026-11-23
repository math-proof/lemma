module

public import Theorem.Matrix.SigmaConjugacy
public import Mathlib.Tactic.Group
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option autoImplicit false

namespace LT.TwistedNorm

section PartialNorm

variable {G : Type*} [Group G]

def sigmaPartialNorm (σ : G →* G) (x : G) : ℕ → G
  | 0 => 1
  | r + 1 => x * σ (sigmaPartialNorm σ x r)

def sigmaNormPow (σ : G →* G) (ℓ : ℕ) (x : G) : G :=
  sigmaPartialNorm σ x ℓ

end PartialNorm


section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] [IsGalois F L] in

variable {n : Type*} [Fintype n] [DecidableEq n]

end Galois

end LT.TwistedNorm

namespace LT.TwistedNorm.GL2

open Matrix

section Companion

variable {K : Type*} [Field K]

def traceDetCompanion (t d : K) : Matrix (Fin 2) (Fin 2) K := !![0, -d; 1, t]

end Companion


end LT.TwistedNorm.GL2


namespace LT.TwistedNorm

section NormEquivVocab

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

def sigmaConjSetoid (σ : L ≃ₐ[F] L) : Setoid (GL (Fin 2) L) where
  r := AutomorphicForm.IsSigmaConj (σ : L →+* L)
  iseqv :=
    { refl := AutomorphicForm.IsSigmaConj.refl (σ : L →+* L)
      symm := by
        intro δ₁ δ₂ h
        obtain ⟨k, rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h
        exact (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mpr ⟨k⁻¹, by rw [map_inv]; group⟩
      trans := by
        intro δ₁ δ₂ δ₃ h h'
        obtain ⟨k, rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h
        obtain ⟨k', rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h'
        exact (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mpr ⟨k * k', by rw [map_mul]; group⟩ }

def SigmaConjClasses (σ : L ≃ₐ[F] L) : Type _ := Quotient (sigmaConjSetoid σ)

def SigmaConjClasses.mk (σ : L ≃ₐ[F] L) (δ : GL (Fin 2) L) : SigmaConjClasses σ :=
  Quotient.mk (sigmaConjSetoid σ) δ

def IsNormRep (σ : L ≃ₐ[F] L) (γ : GL (Fin 2) F) (δ : GL (Fin 2) L) : Prop :=
  ∃ P : GL (Fin 2) L,
    P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ * P
      = Matrix.GeneralLinearGroup.map (algebraMap F L) γ

end NormEquivVocab

section NormEquiv

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

noncomputable def normRep {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) : GL (Fin 2) F :=
  Classical.choose (exists_map_eq_conj_sigmaNormPow hgen δ)

noncomputable def normClassMap {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) :
    SigmaConjClasses σ → ConjClasses (GL (Fin 2) F) :=
  Quotient.lift (fun δ => ConjClasses.mk (normRep hgen δ)) fun δ₁ δ₂ h =>
    ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_of_isNormRep_of_sigmaConj hgen (isNormRep_normRep hgen δ₁)
        (isNormRep_normRep hgen δ₂) ((isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h))

def IsNormClass {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (c : ConjClasses (GL (Fin 2) F)) : Prop :=
  c ∈ Set.range (normClassMap hgen)

end NormEquiv

end LT.TwistedNorm

end
