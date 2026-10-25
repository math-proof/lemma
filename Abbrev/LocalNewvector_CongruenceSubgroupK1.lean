import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


section Padic

variable (p : ℕ) [Fact p.Prime]

abbrev padicK0 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK0 ((p : ℤ_[p])) n

abbrev padicK1 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK1 ((p : ℤ_[p])) n

end Padic

end LocalNewvector

end
