import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheUniqueStabilitySheet
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheUniqueStabilitySheet.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailDensityGauge_eq
  {a b c₀ c₁ : Real}
  {N m : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z₀ z₁ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hc₁ : c₁ ∈ Set.Icc a b)
  (hc₀int : c₀ ∈ Set.Ioo a b)
  (hc₁int : c₁ ∈ Set.Ioo a b)
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
  (hz₁g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₁ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩)
  (hz₁ : sixVertexBetheContinuationProjection z₁ = ⟨c₁, hc₁⟩)
  (htail : ((m + m : Nat) : Real) < sixVertexAnisotropyMagnitude c₀)
  (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀ (sixVertexEvenPositiveHalfProjection m z₀.1.2) = sixVertexSectorTopEigenvalue N (m + m) (by omega) c₀)
  (hwave : sixVertexCoordinateBetheWave (N := N) c₀ z₀.1.2 ≠ 0) :
-- imply
  sixVertexSymmetricBetheEigenvalueKernel c₁ (sixVertexEvenPositiveHalfProjection m z₁.1.2) = sixVertexSectorTopEigenvalue N (m + m) (by omega) c₁ := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailDensityGauge ha hab hc₀ hc₁ hc₀int hc₁int hm hN hhalf rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ z₁ hz₀g hz₁g hz₀ hz₁ htail hbase hwave

/--
[sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheUniqueStabilitySheet.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge_eq
  {a b c₀ c₁ : Real}
  {N m charge : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z₀ z₁ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hc₁ : c₁ ∈ Set.Icc a b)
  (hc₀int : c₀ ∈ Set.Ioo a b)
  (hc₁int : c₁ ∈ Set.Ioo a b)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcharge : N = 2 * (m + m) + 2 * charge)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFixedChargeDensityStabilityErrorOfLower t.1 N charge (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₀ < outer)
  (hz₁g : sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho z₁ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩)
  (hz₁ : sixVertexBetheContinuationProjection z₁ = ⟨c₁, hc₁⟩)
  (htail : ((m + m : Nat) : Real) < sixVertexAnisotropyMagnitude c₀)
  (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀ (sixVertexEvenPositiveHalfProjection m z₀.1.2) = sixVertexSectorTopEigenvalue N (m + m) (by omega) c₀)
  (hwave : sixVertexCoordinateBetheWave (N := N) c₀ z₀.1.2 ≠ 0) :
-- imply
  sixVertexSymmetricBetheEigenvalueKernel c₁ (sixVertexEvenPositiveHalfProjection m z₁.1.2) = sixVertexSectorTopEigenvalue N (m + m) (by omega) c₁ := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge ha hab hc₀ hc₁ hc₀int hc₁int hm hN hcharge rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z₀ z₁ hz₀g hz₁g hz₀ hz₁ htail hbase hwave


-- created on 2026-10-23
