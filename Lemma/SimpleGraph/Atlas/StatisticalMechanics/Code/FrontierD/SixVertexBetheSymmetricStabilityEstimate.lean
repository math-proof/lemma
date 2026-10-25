import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
open StatMech StatMech.FrontierD


/--
[sixVertexFiniteRootDensity_lower_of_weighted_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_lower_of_weighted_close_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {rho : Real → Real}
  {rhoLower eta : Real}
-- given
  (hc : 2 < c)
  (hrhoLower : ∀ x, rhoLower ≤ rho x)
  (hclose : ∀ x, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
-- imply
  ∀ x, rhoLower - eta / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) ≤ sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_lower_of_weighted_close hc p hrhoLower hclose

/--
[sixVertexFiniteRootDensity_lower_at_of_weighted_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_lower_at_of_weighted_close_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {rho : Real → Real}
  {rhoLower eta x : Real}
-- given
  (hc : 2 < c)
  (hrhoLower : rhoLower ≤ rho x)
  (hclose : |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
-- imply
  rhoLower - eta / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) ≤ sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_lower_at_of_weighted_close hc p hrhoLower hclose

/--
[sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  p j.succ - p j.castSucc ≤ 1 / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower hc hN hopen hsol hlower hdensity j

/--
[sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  p 0 - (p (Fin.last n) - 2 * Real.pi) ≤ 1 / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower hc hN hhalf hopen hsol hlower hdensity

/--
[sixVertexCyclicRootPartition_mesh_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_mesh_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k ≤ 1 / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_mesh_of_finiteDensityLower hc hN hhalf hopen hsol hlower hdensity

/--
[abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {lower : Real}
  {f : Real → Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : 0 < n)
  (hhalf : N = 2 * n)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N n p x)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi)) :
-- imply
  |(∑ j, f (p j)) / N - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N n p y| ≤ (C : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * lower)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower hc hN hn hhalf hopen hsol hlower hdensity hf hlip hperiodic

/--
[abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {rho : Real → Real}
  {lower E : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
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
  |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| ≤ sixVertexRootDensityContractionRate c * E + sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
-- proof
  apply StatMech.FrontierD.abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower hc hN hcount hhalf hopen hsol hrho hrhoEq hrhoMass hlower hdensity hE hbound x hx

/--
[abs_weightedFiniteDensity_sub_le_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma abs_weightedFiniteDensity_sub_le_gauge_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {rho : C(Real, Real)}
  {x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ sixVertexWeightedFiniteDensityGauge hc N n p rho := by
-- proof
  apply StatMech.FrontierD.abs_weightedFiniteDensity_sub_le_gauge hc p rho x hx

/--
[sixVertexWeightedFiniteDensityGauge_le_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_le_of_pointwise_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {rho : C(Real, Real)}
  {E : Real}
-- given
  (hc : 2 < c)
  (hE : 0 ≤ E)
  (hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ E) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N n p rho ≤ E := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho hE hbound

/--
[sixVertexWeightedFiniteDensityGauge_selfImproves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_selfImproves_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {rho : C(Real, Real)}
  {lower E : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
  (hE : 0 ≤ E)
  (hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ E) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ sixVertexRootDensityContractionRate c * E + sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_selfImproves hc hN hcount hhalf hopen hsol rho hrhoEq hrhoMass hlower hdensity hE hgauge

/--
[sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {rho : C(Real, Real)}
  {rhoLower inner outer : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ x, rhoLower ≤ rho x)
  (houter : outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2)
  (hinner : sixVertexRootDensityContractionRate c * outer + sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤ inner) :
-- imply
  ¬(inner < sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ∧ sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho < outer) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus hc hN hcount hhalf hopen hsol rho hrhoEq hrhoMass hrhoLower hrho houter hinner

/--
[continuous_sixVertexContinuationWeightedFiniteDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma continuous_sixVertexContinuationWeightedFiniteDensityGauge_eq
  {a b : Real}
  {N n : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (sixVertexContinuationWeightedFiniteDensityGauge ha N n rho) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexContinuationWeightedFiniteDensityGauge ha N n rho

/--
[sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_eq
  {a b : Real}
  {N n r : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hr : r = n + 1)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFiniteDensityContinuumErrorOfLower t.1 N (rhoLower / 2) ≤ inner) :
-- imply
  ∀ z : SixVertexBetheContinuationSpace a b N r, ¬(inner < sixVertexContinuationWeightedFiniteDensityGauge ha N r rho z ∧ sixVertexContinuationWeightedFiniteDensityGauge ha N r rho z < outer) := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus ha hN hr hcount hhalf rho hrhoEq hrhoMass hrhoLower hrho houter hinner

/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {rho : Real → Real}
  {rhoLower eta : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcount : m + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ x, rhoLower ≤ rho x)
  (heta : eta ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2)
  (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x - rho x)| ≤ eta)
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < 2 * Real.pi) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose hc hm hN hcount hopen hsol hrhoLower hrho heta hclose hmargin

/--
[sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective_eq
  {a b : Real}
  {N m : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower outer : Real}
  {z : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hm : 0 < m)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hcount : m + m ≤ N)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hgauge : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z < outer) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective ha hm hN hhalf hcount rho hrhoLower hrho houter hmargin z hgauge

/--
[exists_sixVertexContinuousEvenSymmetricBetheBranch_of_densityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean)
-/
@[path]
private lemma exists_sixVertexContinuousEvenSymmetricBetheBranch_of_densityGauge_eq
  {a b c₀ : Real}
  {N m : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hm : 0 < m)
  (hN : 0 < N)
  (hhalf : N = 2 * (m + m))
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFiniteDensityContinuumErrorOfLower t.1 N (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₀ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousEvenSymmetricBetheBranch_of_densityGauge ha hab hc₀ hm hN hhalf rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ hz₀g hz₀


-- created on 2026-10-23
