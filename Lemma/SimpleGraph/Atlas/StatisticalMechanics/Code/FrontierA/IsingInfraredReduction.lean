import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
open Finset Filter Set Topology StatMech StatMech.FrontierA


/--
[finiteTorusQuadratic_addChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma finiteTorusQuadratic_addChar_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → ℝ}
  {chi : AddChar Gamma ℂ} :
-- imply
  finiteTorusQuadratic G chi = (Fintype.card Gamma : ℂ) * finiteTorusFourierCoeff G chi := by
-- proof
  apply StatMech.FrontierA.finiteTorusQuadratic_addChar G chi

/--
[finiteTorus_addChar_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma finiteTorus_addChar_sum_eq_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {chi : AddChar Gamma ℂ}
-- given
  (hchi : chi ≠ 0) :
-- imply
  (∑ x : Gamma, chi x) = 0 := by
-- proof
  apply StatMech.FrontierA.finiteTorus_addChar_sum_eq_zero chi hchi

/--
[finiteTorus_fourier_bound_of_gaussianDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma finiteTorus_fourier_bound_of_gaussianDomination_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → ℝ}
  {inverseEnergy : (Gamma → ℂ) → ℝ}
  {C delta : ℝ}
  {chi : AddChar Gamma ℂ}
-- given
  (hchi : chi ≠ 0)
  (hpsd : IsPositiveSemidefiniteTorusKernel G)
  (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
  (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
-- imply
  0 ≤ (finiteTorusFourierCoeff G chi).re ∧ (finiteTorusFourierCoeff G chi).re ≤ C / delta := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_bound_of_gaussianDomination G inverseEnergy C delta chi hchi hpsd hgauss hmode

/--
[infrared_fourier_bound_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma infrared_fourier_bound_of_tendsto_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {fourier dispersion : ℕ → ℝ}
  {C fourierLimit dispersionLimit : ℝ}
-- given
  (hfourier : Tendsto fourier atTop (nhds fourierLimit))
  (hdispersion : Tendsto dispersion atTop (nhds dispersionLimit))
  (hdispersionLimit : 0 < dispersionLimit)
  (hnonneg : ∀ n, 0 ≤ fourier n)
  (hbound : ∀ n, fourier n ≤ C / dispersion n) :
-- imply
  0 ≤ fourierLimit ∧ fourierLimit ≤ C / dispersionLimit := by
-- proof
  apply StatMech.FrontierA.infrared_fourier_bound_of_tendsto fourier dispersion C fourierLimit dispersionLimit hfourier hdispersion hdispersionLimit hnonneg hbound

/--
[infrared_average_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma infrared_average_tendsto_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {averageFourier averageReciprocal : ℕ → ℝ}
  {C : ℝ}
-- given
  (hnonneg : ∀ n, 0 ≤ averageFourier n)
  (hbound : ∀ n, averageFourier n ≤ C * averageReciprocal n)
  (hreciprocal : Tendsto averageReciprocal atTop (nhds 0)) :
-- imply
  Tendsto averageFourier atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.infrared_average_tendsto_zero averageFourier averageReciprocal C hnonneg hbound hreciprocal

/--
[longRangeOrder_eq_zero_of_infrared_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean)
-/
@[path]
private lemma longRangeOrder_eq_zero_of_infrared_average_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {averageFourier averageReciprocal : ℕ → ℝ}
  {C m : ℝ}
-- given
  (hm : 0 ≤ m)
  (hmle : ∀ n, m ^ 2 ≤ averageFourier n)
  (hnonneg : ∀ n, 0 ≤ averageFourier n)
  (hbound : ∀ n, averageFourier n ≤ C * averageReciprocal n)
  (hreciprocal : Tendsto averageReciprocal atTop (nhds 0)) :
-- imply
  m = 0 := by
-- proof
  apply StatMech.FrontierA.longRangeOrder_eq_zero_of_infrared_average averageFourier averageReciprocal C m hm hmle hnonneg hbound hreciprocal


-- created on 2026-10-23
