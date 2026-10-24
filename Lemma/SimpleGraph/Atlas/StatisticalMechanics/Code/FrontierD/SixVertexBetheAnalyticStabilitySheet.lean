import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
open Filter Topology StatMech StatMech.FrontierD


/--
[exists_sixVertexContinuousBetheBranch_of_compactComponent_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticStabilitySheet.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_compactComponent_mem_eq
  {a b c₀ : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)}
  {z₀ : C}
-- given
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hcompact : IsCompact C)
  (hlocal : IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C))
  (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.1.2 ∧ ∀ t ∈ Set.Icc a b, ∃ z : SixVertexBetheContinuationSpace a b N n, z ∈ C ∧ z.1.1 = t ∧ z.1.2 = roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_compactComponent_mem hab hc₀ C hcompact hlocal z₀ hz₀

/--
[analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticStabilitySheet.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch_eq
  {a b : Real}
  {N m : Nat}
  {roots : C(Real, Fin (m + m) → Real)}
-- given
  (ha : 2 < a)
  (hopen : ∀ t ∈ Set.Ioo a b, SixVertexOpenRootSimplex (roots t))
  (hsol : ∀ t ∈ Set.Ioo a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t))
  (hjac : ∀ t ∈ Set.Ioo a b, Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m t (sixVertexEvenPositiveHalfProjection m (roots t)))) :
-- imply
  AnalyticOnNhd Real roots (Set.Ioo a b) := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexContinuousEvenSymmetricBetheBranch ha roots hopen hsol hjac

/--
[exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticStabilitySheet.lean)
-/
@[path]
private lemma exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge_eq
  {a b c₀ : Real}
  {N m : Nat}
  {g : SixVertexBetheContinuationSpace a b N (m + m) → Real}
  {inner outer : Real}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hg : Continuous g)
  (hio : inner < outer)
  (hgap : ∀ z, ¬(inner < g z ∧ g z < outer))
  (hjac : ∀ z, g z < outer → Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2)))
  (hz₀g : g z₀ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ (∀ t ∈ Set.Icc a b, SixVertexOpenRootSimplex (roots t) ∧ SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧ AnalyticOnNhd Real roots (Set.Ioo a b) ∧ ∀ t (ht : t ∈ Set.Icc a b), ∃ z : SixVertexBetheContinuationSpace a b N (m + m), g z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge ha hab hc₀ hN hhalf g hg hio hgap hjac z₀ hz₀g hz₀

/--
[exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticStabilitySheet.lean)
-/
@[path]
private lemma exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge_eq
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
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ (∀ t ∈ Set.Icc a b, SixVertexOpenRootSimplex (roots t) ∧ SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧ AnalyticOnNhd Real roots (Set.Ioo a b) ∧ ∀ t (ht : t ∈ Set.Icc a b), ∃ z : SixVertexBetheContinuationSpace a b N (m + m), sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge ha hab hc₀ hm hN hhalf rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ hz₀g hz₀


-- created on 2026-10-23
