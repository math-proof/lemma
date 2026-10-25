import Mathlib

open Matrix MeasureTheory

namespace AutomorphicForm

section Unipotent

variable {R : Type*} [CommRing R]

private theorem unipotent_mul_unipotent (x y : R) :
    !![1, x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def unipotentGL2 (x : R) : GL (Fin 2) R where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by rw [unipotent_mul_unipotent, add_neg_cancel, Matrix.one_fin_two]
  inv_val := by rw [unipotent_mul_unipotent, neg_add_cancel, Matrix.one_fin_two]

@[simp] theorem unipotentGL2_coe (x : R) :
    (unipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, x; 0, 1] := rfl

@[simp] theorem unipotentGL2_zero : unipotentGL2 (0 : R) = 1 := by
  ext i j; simp [unipotentGL2, Matrix.one_fin_two]

theorem unipotentGL2_add (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y := by
  ext i j; simp only [unipotentGL2, Units.val_mul, unipotent_mul_unipotent]

def unipotentGL2Hom : Multiplicative R →* GL (Fin 2) R where
  toFun x := unipotentGL2 x.toAdd
  map_one' := unipotentGL2_zero
  map_mul' x y := unipotentGL2_add x.toAdd y.toAdd

end Unipotent

section ConstantTerm

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

def constantTermIntegrand (u : Q → G) (f : G → ℂ) (g : G) : Q → ℂ :=
  fun q => f (u q * g)

noncomputable def constantTerm (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g : G) : ℂ :=
  ∫ q, constantTermIntegrand u f g q ∂μ

@[simp] theorem constantTerm_zero (μ : Measure Q) (u : Q → G) (g : G) :
    constantTerm μ u (fun _ => (0 : ℂ)) g = 0 := by
  simp [constantTerm, constantTermIntegrand]

@[simp] theorem constantTerm_const (μ : Measure Q) [IsProbabilityMeasure μ] (u : Q → G)
    (c : ℂ) (g : G) : constantTerm μ u (fun _ => c) g = c := by
  simp [constantTerm, constantTermIntegrand, integral_const, measureReal_def]

def IsCuspidalFn (μ : Measure Q) (u : Q → G) (f : G → ℂ) : Prop :=
  ∀ g : G, constantTerm μ u f g = 0

end ConstantTerm

end AutomorphicForm
