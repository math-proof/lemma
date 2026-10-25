import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

structure IsLocallyFreeOfRank (n : ℕ) (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))

end AlgebraicGeometry.Scheme.Modules
