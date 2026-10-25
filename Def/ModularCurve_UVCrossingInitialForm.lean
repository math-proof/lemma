import Mathlib
import Lemma.ModularCurve.UVCrossingModel
import Def.ModularCurve_UVCrossingGaussOrder
import Def.ModularCurve_UVCrossingDominantIndices

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

open IsLocalRing

variable {W : Type u} [CommRing W]

def unitPart (ϖ c : W) : W :=
  (pow_multiplicity_dvd ϖ c).choose


variable [IsDomain W] [IsDiscreteValuationRing W]

open Classical in

def leadingResidue (ϖ c : W) : ResidueField W :=
  if c = 0 then 0 else residue W (unitPart ϖ c)

open Classical in

def initialFormOfSet (ϖ : W) (S : Set ℤ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  if hS : S.Finite then
    ∑ n ∈ hS.toFinset, LaurentPolynomial.C (leadingResidue ϖ (nfCoeff ab n)) * LaurentPolynomial.T n
  else 0


def initialForm (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  initialFormOfSet ϖ (dominantIndices v E t ab) ab

end

end ModularCurve.UVCrossingModel
