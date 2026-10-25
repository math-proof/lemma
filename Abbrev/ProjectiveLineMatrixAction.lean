import Mathlib
import Instance.ModularCurve_ProjectiveLine

namespace ModularCurve.ProjectiveLine

variable {R : Type*} [CommRing R]

end ModularCurve.ProjectiveLine

namespace HeckeEis

open ModularCurve
open scoped MatrixGroups

abbrev redMat (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  M.map (Int.castRingHom (ZMod N))

section Rep

variable (N : ℕ) (K : Type*) [CommRing K]

end Rep

end HeckeEis
