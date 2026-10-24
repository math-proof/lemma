import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace FLT.ExplicitLift

open Matrix Zsqrtd

theorem neg_one_sq_eq_neg_two : (-1 : ZMod 3) * (-1) = ((-2 : ℤ) : ZMod 3) := by decide

noncomputable def red : ℤ√(-2) →+* ZMod 3 :=
  Zsqrtd.lift ⟨-1, neg_one_sq_eq_neg_two⟩

def sbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![-1, 1; -1, 0]

def tbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; 1, 1]

def Slift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩]

def Tlift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩]

end FLT.ExplicitLift
