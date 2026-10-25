import Mathlib
import Instance.LocalLanglands_HeckePair
import Def.LocalLanglands_CartanDecomposition

set_option autoImplicit false

open Matrix

noncomputable section

namespace LocalGL2

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range


section Transpose

variable {A : Type*} [CommRing A]

def transposeGL (x : GL (Fin 2) A) : GL (Fin 2) A where
  val := x.valᵀ
  inv := x.invᵀ
  val_inv := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]

end Transpose

end LocalGL2

end
