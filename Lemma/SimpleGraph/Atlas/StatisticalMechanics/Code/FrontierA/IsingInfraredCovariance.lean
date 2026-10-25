import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredCovariance
open Finset StatMech StatMech.FrontierA


/--
[finiteTorusQuadratic_re_eq_stationaryGram_squares](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean)
-/
@[path]
private lemma finiteTorusQuadratic_re_eq_stationaryGram_squares_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  [Fintype Omega]
  {G : Gamma → ℝ}
  {weight : Omega → ℝ}
  {field : Omega → Gamma → ℝ}
  {f : Gamma → ℂ}
-- given
  (hrep : forall x z, G z = ∑ omega, weight omega * field omega x * field omega (x + z)) :
-- imply
  (finiteTorusQuadratic G f).re = ∑ omega, weight omega * ((∑ x, field omega x * (f x).re) ^ 2 + (∑ x, field omega x * (f x).im) ^ 2) := by
-- proof
  apply StatMech.FrontierA.finiteTorusQuadratic_re_eq_stationaryGram_squares G weight field hrep f

/--
[isPositiveSemidefiniteTorusKernel_of_stationaryGram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean)
-/
@[path]
private lemma isPositiveSemidefiniteTorusKernel_of_stationaryGram_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  [Fintype Omega]
  {G : Gamma → ℝ}
  {weight : Omega → ℝ}
  {field : Omega → Gamma → ℝ}
-- given
  (hrep : HasFiniteStationaryGramRepresentation G weight field) :
-- imply
  IsPositiveSemidefiniteTorusKernel G := by
-- proof
  apply StatMech.FrontierA.isPositiveSemidefiniteTorusKernel_of_stationaryGram G weight field hrep

/--
[finiteTorus_fourier_bound_of_stationaryGram_gaussianDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean)
-/
@[path]
private lemma finiteTorus_fourier_bound_of_stationaryGram_gaussianDomination_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  [Fintype Omega]
  {G : Gamma → ℝ}
  {weight : Omega → ℝ}
  {field : Omega → Gamma → ℝ}
  {inverseEnergy : (Gamma → ℂ) → ℝ}
  {C delta : ℝ}
  {chi : AddChar Gamma ℂ}
-- given
  (hchi : chi ≠ 0)
  (hrep : HasFiniteStationaryGramRepresentation G weight field)
  (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
  (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
-- imply
  0 ≤ (finiteTorusFourierCoeff G chi).re ∧ (finiteTorusFourierCoeff G chi).re ≤ C / delta := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_bound_of_stationaryGram_gaussianDomination G weight field inverseEnergy C delta chi hchi hrep hgauss hmode

/--
[finiteIsing_hasFiniteStationaryGramRepresentation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean)
-/
@[path]
private lemma finiteIsing_hasFiniteStationaryGramRepresentation_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  [DecidableEq Gamma]
  {H : SimpleGraph Gamma}
  [DecidableRel H.Adj]
  {G : Gamma → ℝ}
-- given
  (beta h : ℝ)
  (hstationary : ∀ x z, G z = ∑ sigma, Ising.isingProb H beta h sigma * (Ising.spin sigma x - Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) * (Ising.spin sigma (x + z) - Ising.isingExpectation H beta h (fun tau => Ising.spin tau (x + z)))) :
-- imply
  HasFiniteStationaryGramRepresentation G (Ising.isingProb H beta h) (fun sigma x => Ising.spin sigma x - Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) := by
-- proof
  apply StatMech.FrontierA.finiteIsing_hasFiniteStationaryGramRepresentation H beta h G hstationary

/--
[finiteIsingTorus_fourier_bound_of_gaussianDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean)
-/
@[path]
private lemma finiteIsingTorus_fourier_bound_of_gaussianDomination_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  [DecidableEq Gamma]
  {H : SimpleGraph Gamma}
  [DecidableRel H.Adj]
  {G : Gamma → ℝ}
  {inverseEnergy : (Gamma → ℂ) → ℝ}
  {C delta : ℝ}
  {chi : AddChar Gamma ℂ}
-- given
  (beta h : ℝ)
  (hchi : chi ≠ 0)
  (hstationary : ∀ x z, G z = ∑ sigma, Ising.isingProb H beta h sigma * (Ising.spin sigma x - Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) * (Ising.spin sigma (x + z) - Ising.isingExpectation H beta h (fun tau => Ising.spin tau (x + z))))
  (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
  (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
-- imply
  0 ≤ (finiteTorusFourierCoeff G chi).re ∧ (finiteTorusFourierCoeff G chi).re ≤ C / delta := by
-- proof
  apply StatMech.FrontierA.finiteIsingTorus_fourier_bound_of_gaussianDomination H beta h G inverseEnergy C delta chi hchi hstationary hgauss hmode


-- created on 2026-10-23
