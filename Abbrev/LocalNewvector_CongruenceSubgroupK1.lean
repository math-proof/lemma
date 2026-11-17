module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

@[expose] public noncomputable section

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
