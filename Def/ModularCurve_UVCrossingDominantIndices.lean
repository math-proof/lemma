import Mathlib
import Lemma.ModularCurve.UVCrossingModel
import Def.ModularCurve_UVCrossingGaussOrder

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]

def nfCoeff (ab : PowerSeries W × PowerSeries W) : ℤ → W
  | Int.ofNat i => PowerSeries.coeff i ab.1
  | Int.negSucc j => PowerSeries.coeff (j + 1) ab.2

def nfExponent : ℤ → (Fin 2 →₀ ℕ)
  | Int.ofNat i => Finsupp.single 0 i
  | Int.negSucc j => Finsupp.single 1 (j + 1)

def termOrder (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) : ℕ∞ :=
  v (nfCoeff ab n) + (annulusWeight E t (nfExponent n) : ℕ∞)

def dominantIndices (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) : Set ℤ :=
  {n | termOrder v E t ab n = repGaussOrder v E t (inU ab.1 + inV ab.2)}

def circleIndexDrop (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) : ℕ :=
  (sSup (dominantIndices v E t ab) - sInf (dominantIndices v E t ab)).toNat

end

end ModularCurve.UVCrossingModel
