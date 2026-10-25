import Mathlib
import Lemma.ModularCurve.UVCrossingModel
import Lemma.ModularCurve.UVCrossingGaussOrder
import Def.ModularCurve_UVCrossingDominantIndices
import Def.ModularCurve_UVCrossingInitialForm

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

open IsLocalRing

variable {W : Type u} [CommRing W]


theorem pow_multiplicity_mul_unitPart (ϖ c : W) : ϖ ^ multiplicity ϖ c * unitPart ϖ c = c :=
  (pow_multiplicity_dvd ϖ c).choose_spec.symm

variable [IsDomain W] [IsDiscreteValuationRing W]


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


theorem initialForm_def (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    initialForm ϖ v E t ab = initialFormOfSet ϖ (dominantIndices v E t ab) ab := rfl

end

end ModularCurve.UVCrossingModel
