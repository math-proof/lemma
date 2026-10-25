import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm

noncomputable section

namespace AutomorphicForm

section BorelCommRing

variable (A : Type*) [CommRing A]

def borelSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hy
    show ((x * y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' := by
    intro x hx
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    show ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']


variable {A}

def borelDiagFst : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      val_inv := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          mul_zero, add_zero] at h1
      inv_val := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          mul_zero, add_zero] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hc : ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := c.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hc, mul_zero, add_zero]

def borelDiagSnd : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      val_inv := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          zero_mul, zero_add] at h1
      inv_val := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          zero_mul, zero_add] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hb, zero_mul, zero_add]

end BorelCommRing

end AutomorphicForm

end
