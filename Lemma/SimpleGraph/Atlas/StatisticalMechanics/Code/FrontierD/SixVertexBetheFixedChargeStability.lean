import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeStability
open StatMech StatMech.FrontierD


/--
[intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∫ x in p (Fin.last n) - 2 * Real.pi..p 0, sixVertexFiniteRootDensity c N (n + 1) p x = (2 * (r : Real) + 1) / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge hc hN hcharge hsol

/--
[sixVertexCyclicRootPartition_densityMass_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_densityMass_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∀ k < n + 1, ∫ x in sixVertexCyclicRootPartition p k.. sixVertexCyclicRootPartition p (k + 1), sixVertexFiniteRootDensity c N (n + 1) p x = if k = 0 then (2 * (r : Real) + 1) / N else 1 / N := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_densityMass_fixedCharge hc hN hcharge hsol

/--
[sixVertexBetheSolution_boundarySpacing_upper_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexBetheSolution_boundarySpacing_upper_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  p 0 - (p (Fin.last n) - 2 * Real.pi) ≤ (2 * (r : Real) + 1) / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_boundarySpacing_upper_fixedCharge hc hN hcharge hopen hsol hlower hdensity

/--
[sixVertexCyclicRootPartition_mesh_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_mesh_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k ≤ (2 * (r : Real) + 1) / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_mesh_fixedCharge hc hN hcharge hopen hsol hlower hdensity

/--
[abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {mesh : Real}
  {f : Real → Real}
  {C : NNReal}
  {F : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hmesh : ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k ≤ mesh)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hfBound : ∀ x, |f x| ≤ F) :
-- imply
  |∑ k ∈ Finset.range (n + 1), (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) - ∫ x in sixVertexCyclicRootPartition p 0.. sixVertexCyclicRootPartition p (n + 1), f x * sixVertexFiniteRootDensity c N (n + 1) p x| ≤ (C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh * (2 * Real.pi) + (2 * (r : Real) / N) * F := by
-- proof
  apply StatMech.FrontierD.abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge hc hN hcharge hopen hsol hmesh hf hlip hfBound

/--
[sixVertexRootDensityKernelUniformBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexRootDensityKernelUniformBound_nonneg_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexRootDensityKernelUniformBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernelUniformBound_nonneg hc

/--
[abs_sixVertexRootDensityKernel_le_uniformBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma abs_sixVertexRootDensityKernel_le_uniformBound_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y| ≤ sixVertexRootDensityKernelUniformBound c := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRootDensityKernel_le_uniformBound hc x y

/--
[sixVertexRootDensityKernel_contraction_of_fixedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_contraction_of_fixedMass_eq
  {c : Real}
  {e : Real → Real}
  {E m : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (he : Continuous e)
  (hE : 0 ≤ E)
  (hm : 0 ≤ m)
  (hmass : (∫ y in -Real.pi..Real.pi, e y / sixVertexRootDensityWeight c y) = m)
  (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E) :
-- imply
  |(1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, (sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y) * e y| ≤ sixVertexRootDensityContractionRate c * (E + (m / (2 * Real.pi)) * ((sixVertexAnisotropyMagnitude c + 1) / sixVertexRootDensityScale c)) + (m / (2 * Real.pi)) * sixVertexRootDensityKernelUniformBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_contraction_of_fixedMass hc he hE hm hmass hbound x

/--
[sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div_eq
  {c lower : Real}
  {r : Nat}
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower = sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div c lower r hN

/--
[exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici_eq
  {a lower : Real}
  {r : Nat}
-- given
  (ha : 2 < a)
  (hlower : 0 < lower) :
-- imply
  ∃ B : Real, 0 < B ∧ ∀ {N : Nat}, 0 < N → ∀ c, a ≤ c → sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower ≤ B / N := by
-- proof
  apply StatMech.FrontierD.exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici ha hlower r

/--
[abs_sixVertexFiniteConvolutionDefect_le_fixedCharge_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma abs_sixVertexFiniteConvolutionDefect_le_fixedCharge_of_lower_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  |sixVertexFiniteConvolutionDefect c N (n + 1) p x| ≤ sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) + (2 * (r : Real) / N) * sixVertexRootDensityKernelUniformBound c := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexFiniteConvolutionDefect_le_fixedCharge_of_lower hc hN hcharge hopen hsol hlower hdensity x

/--
[abs_finiteRootDensity_sub_continuumDensity_weighted_le_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma abs_finiteRootDensity_sub_continuumDensity_weighted_le_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {rho : Real → Real}
  {lower E : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hrho : Continuous rho)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
  (hE : 0 ≤ E)
  (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N (n + 1) p y - rho y)| ≤ E)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| ≤ sixVertexRootDensityContractionRate c * E + sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
-- proof
  apply StatMech.FrontierD.abs_finiteRootDensity_sub_continuumDensity_weighted_le_fixedCharge hc hN hcharge hopen hsol hrho hrhoEq hrhoMass hlower hdensity hE hbound x hx

/--
[sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {rho : C(Real, Real)}
  {lower E : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
  (hE : 0 ≤ E)
  (hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ E) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ sixVertexRootDensityContractionRate c * E + sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge hc hN hcharge hopen hsol rho hrhoEq hrhoMass hlower hdensity hE hgauge

/--
[sixVertexFiniteRootDensity_lower_half_of_weightedGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_lower_half_of_weightedGauge_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {rho : C(Real, Real)}
  {rhoLower outer : Real}
-- given
  (hc : 2 < c)
  (hrho : forall x, rhoLower <= rho x)
  (houter : outer <= rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2)
  (hgauge : sixVertexWeightedFiniteDensityGauge hc N n p rho <= outer) :
-- imply
  forall x, rhoLower / 2 <= sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_lower_half_of_weightedGauge hc rho hrho houter hgauge

/--
[sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge_eq
  {c1 c2 : Real}
  {N n : Nat}
  {p q : Fin n -> Real}
-- given
  (hc1 : 2 < c1)
  (hc2 : 2 < c2)
  (hc : c1 = c2)
  (hp : p = q) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc1 N n p (sixVertexFourierPhysicalDensityMap hc1) = sixVertexWeightedFiniteDensityGauge hc2 N n q (sixVertexFourierPhysicalDensityMap hc2) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge hc1 hc2 hc hp

/--
[sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {rho : C(Real, Real)}
  {rhoLower inner outer : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ x, rhoLower ≤ rho x)
  (houter : outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2)
  (hinner : sixVertexRootDensityContractionRate c * outer + sixVertexFixedChargeDensityStabilityErrorOfLower c N r (rhoLower / 2) ≤ inner) :
-- imply
  ¬(inner < sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ∧ sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho < outer) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge hc hN hcharge hopen hsol rho hrhoEq hrhoMass hrhoLower hrho houter hinner

/--
[sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge_eq
  {a b : Real}
  {N n q r : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hq : q = n + 1)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFixedChargeDensityStabilityErrorOfLower t.1 N r (rhoLower / 2) ≤ inner) :
-- imply
  ∀ z : SixVertexBetheContinuationSpace a b N q, ¬(inner < sixVertexContinuationWeightedFiniteDensityGauge ha N q rho z ∧ sixVertexContinuationWeightedFiniteDensityGauge ha N q rho z < outer) := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge ha hN hq hcharge rho hrhoEq hrhoMass hrhoLower hrho houter hinner

/--
[exists_sixVertexContinuousEvenSymmetricBetheBranch_of_fixedChargeDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma exists_sixVertexContinuousEvenSymmetricBetheBranch_of_fixedChargeDensityGauge_eq
  {a b c₀ : Real}
  {N m r : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcharge : N = 2 * (m + m) + 2 * r)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFixedChargeDensityStabilityErrorOfLower t.1 N r (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₀ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousEvenSymmetricBetheBranch_of_fixedChargeDensityGauge ha hab hc₀ hm hN hcharge rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ hz₀g hz₀

/--
[exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge_eq
  {a b c₀ : Real}
  {N m r : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcharge : N = 2 * (m + m) + 2 * r)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFixedChargeDensityStabilityErrorOfLower t.1 N r (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₀ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ (∀ t ∈ Set.Icc a b, SixVertexOpenRootSimplex (roots t) ∧ SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧ AnalyticOnNhd Real roots (Set.Ioo a b) ∧ ∀ t (_ht : t ∈ Set.Icc a b), ∃ z : SixVertexBetheContinuationSpace a b N (m + m), sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge ha hab hc₀ hm hN hcharge rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ hz₀g hz₀

/--
[sixVertexWeightedFiniteDensityGauge_le_fixedChargeAnisotropyError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_le_fixedChargeAnisotropyError_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin n → Real}
  {rho : C(Real, Real)}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * n + 2 * r)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hrhoNonneg : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ rho y) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N n p rho ≤ ((1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) + (r : Real) / N) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_le_fixedChargeAnisotropyError hc hN hcharge p rho hrhoEq hrhoMass hrhoNonneg


-- created on 2026-10-23
