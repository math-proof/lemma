import Mathlib

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

def addPoly (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  X (0, n) + X (1, n) + ∑ i ∈ Finset.range n, X (0, i) * X (1, n - 1 - i)


variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (addPoly n))

end BigWittLaw

end MvFormalGroup

end
