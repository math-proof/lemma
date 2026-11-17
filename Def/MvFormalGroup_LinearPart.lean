module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open MvPowerSeries

namespace MvFormalGroup

variable {g h : ℕ} {R : Type*} [CommRing R]

noncomputable def linearPart (φ : Fin h → MvPowerSeries (Fin g) R) : Matrix (Fin h) (Fin g) R :=
  Matrix.of fun i j => (φ i).coeff (Finsupp.single j 1)

end MvFormalGroup
