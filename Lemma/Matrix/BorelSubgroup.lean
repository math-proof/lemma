import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm
import Def.AutomorphicForm_BorelSubgroup
import Abbrev.AutomorphicForm_BorelSubgroup

noncomputable section

namespace AutomorphicForm

section BorelCommRing

variable (A : Type*) [CommRing A]


@[simp] theorem mem_borelSubgroup_iff {x : GL (Fin 2) A} :
    x ∈ borelSubgroup A ↔ (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := Iff.rfl

theorem borel_entry_one_zero (b : ↥(borelSubgroup A)) :
    ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2

variable {A}


@[simp] theorem borelDiagFst_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagFst b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 := rfl

@[simp] theorem borelDiagSnd_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagSnd b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 := rfl

theorem det_borel_eq_diag_mul {x : GL (Fin 2) A} (hx : x ∈ borelSubgroup A) :
    Matrix.GeneralLinearGroup.det x
      = borelDiagFst (⟨x, hx⟩ : ↥(borelSubgroup A))
        * borelDiagSnd (⟨x, hx⟩ : ↥(borelSubgroup A)) := by
  apply Units.ext
  have hb : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
  show (x : Matrix (Fin 2) (Fin 2) A).det
      = (x : Matrix (Fin 2) (Fin 2) A) 0 0 * (x : Matrix (Fin 2) (Fin 2) A) 1 1
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero]

theorem unipotentGL2_mem_borelSubgroup (x : A) : unipotentGL2 x ∈ borelSubgroup A := by
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  rw [unipotentGL2_coe]
  simp

theorem borelDiagFst_unipotentGL2 (x : A) :
    borelDiagFst ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
  rw [unipotentGL2_coe]
  simp

theorem borelDiagSnd_unipotentGL2 (x : A) :
    borelDiagSnd ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
  rw [unipotentGL2_coe]
  simp

end BorelCommRing

section AdelicBorel

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem globalPoints_apply (γ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem globalPoints_mem_adelicBorel {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) : globalPoints R K γ ∈ adelicBorel R K := by
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hγ
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [globalPoints_apply, hγ', map_zero]

theorem borelDiagFst_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagFst (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagFst (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)
  exact globalPoints_apply R K γ 0 0

theorem borelDiagSnd_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagSnd (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagSnd (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)
  exact globalPoints_apply R K γ 1 1

theorem centralScalar_mem_adelicBorel (z : (AdeleRing R K)ˣ) :
    centralScalar R K z ∈ adelicBorel R K := by
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem borelDiagFst_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagFst (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem borelDiagSnd_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagSnd (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

end AdelicBorel

end AutomorphicForm

end
