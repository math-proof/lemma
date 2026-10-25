import Mathlib
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]

abbrev vertexDiscr (q : ℕ) : R[X] := X ^ q - X

abbrev chartVRing (q : ℕ) : Type := Localization.Away (vertexDiscr R q)

namespace chartVRing

variable (q : ℕ)

end chartVRing

abbrev edgeRel (π : R) : MvPolynomial (Fin 2) R := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π

abbrev edgeDiscr (q : ℕ) : MvPolynomial (Fin 2) R :=
  (MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)


section Level

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q n : ℕ)

abbrev truncRing : Type := 𝒪 ⧸ Ideal.span {π ^ (n + 1)}

abbrev chartVRingMod : Type := chartVRing (truncRing 𝒪 π n) q

end Level

end ChartRings

end FormalOmega
end CerednikDrinfeld

end
