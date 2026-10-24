import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

open Matrix MatrixGroups Subgroup

namespace ModularCurve

section Elementary

variable {R : Type*} [CommRing R]

def upperElem (c : R) : SL(2, R) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def lowerElem (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma upperElem_coe (c : R) :
    (upperElem c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] := rfl

@[simp] lemma lowerElem_coe (c : R) :
    (lowerElem c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl

lemma upperElem_mul (a b : R) : upperElem a * upperElem b = upperElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma lowerElem_mul (a b : R) : lowerElem a * lowerElem b = lowerElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma upperElem_zero : upperElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] lemma lowerElem_zero : lowerElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma upperElem_pow (a : R) (n : ℕ) : upperElem a ^ n = upperElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, upperElem_mul]
    congr 1
    push_cast
    ring

lemma lowerElem_pow (a : R) (n : ℕ) : lowerElem a ^ n = lowerElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, lowerElem_mul]
    congr 1
    push_cast
    ring

def elemSet (R : Type*) [CommRing R] : Set SL(2, R) :=
  Set.range upperElem ∪ Set.range lowerElem

lemma upperElem_mem_closure_elemSet (c : R) : upperElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inl ⟨c, rfl⟩)

lemma lowerElem_mem_closure_elemSet (c : R) : lowerElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inr ⟨c, rfl⟩)

end Elementary

end ModularCurve
