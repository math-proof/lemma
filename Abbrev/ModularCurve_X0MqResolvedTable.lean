import Mathlib
import Structure.AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers

set_option autoImplicit false

namespace ModularCurve
open MazurRapoportAppendix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev X0MqComponents (e : ι → ℕ) : Type _ := Fin 2 ⊕ (Σ x : ι, Fin (e x - 1))

end ModularCurve
