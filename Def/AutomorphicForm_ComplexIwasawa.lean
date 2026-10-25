import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

open ComplexConjugate

namespace AutomorphicForm.ComplexIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

def radC (z : ℂ) : ℝ := Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

end AutomorphicForm.ComplexIwasawa

end
