import Mathlib
import Lemma.Definitions.Def_ModularCurve_UVCrossingModel
import Lemma.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Lemma.Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

open IsLocalRing

variable {W : Type u} [CommRing W]

def unitPart (ϖ c : W) : W :=
  (pow_multiplicity_dvd ϖ c).choose

theorem pow_multiplicity_mul_unitPart (ϖ c : W) : ϖ ^ multiplicity ϖ c * unitPart ϖ c = c :=
  (pow_multiplicity_dvd ϖ c).choose_spec.symm

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

open Classical in

theorem initialFormOfSet_apply (ϖ : W) {S : Set ℤ} (hS : S.Finite)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    (initialFormOfSet ϖ S ab).coeff n = if n ∈ S then leadingResidue ϖ (nfCoeff ab n) else 0 := by
  classical
  rw [initialFormOfSet, dif_pos hS]
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  erw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset]

def initialForm (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  initialFormOfSet ϖ (dominantIndices v E t ab) ab

theorem initialForm_def (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    initialForm ϖ v E t ab = initialFormOfSet ϖ (dominantIndices v E t ab) ab := rfl

end

end ModularCurve.UVCrossingModel
