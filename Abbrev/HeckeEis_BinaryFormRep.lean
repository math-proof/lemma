import Mathlib
import Instance.ProjectiveLineMatrixAction

namespace HeckeEis

open MvPolynomial ModularCurve
open scoped MatrixGroups

section BinaryForms

variable (K : Type*) [CommRing K]

abbrev BinaryForm (n : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K n

end BinaryForms

section Eval

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

end Eval

end HeckeEis
