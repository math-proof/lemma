import Mathlib

namespace EisensteinSeries

noncomputable def eisensteinG (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : UpperHalfPlane) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ v = a}, eisSummand k v.1 z

end EisensteinSeries
