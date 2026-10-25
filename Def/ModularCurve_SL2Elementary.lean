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


def elemSet (R : Type*) [CommRing R] : Set SL(2, R) :=
  Set.range upperElem ∪ Set.range lowerElem

end Elementary

end ModularCurve
