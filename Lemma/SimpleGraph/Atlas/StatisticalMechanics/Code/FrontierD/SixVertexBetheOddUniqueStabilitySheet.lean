import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddUniqueStabilitySheet
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexOddSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddUniqueStabilitySheet.lean)
-/
@[path]
private lemma sixVertexOddSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge_eq
  {a b c0 c1 : Real}
  {N m charge : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
  {z0 z1 : SixVertexBetheContinuationSpace a b N ((m + 1) + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc0 : c0 ∈ Set.Icc a b)
  (hc1 : c1 ∈ Set.Icc a b)
  (hc0int : c0 ∈ Set.Ioo a b)
  (hc1int : c1 ∈ Set.Ioo a b)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcharge : N = 2 * ((m + 1) + m) + 2 * charge)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFixedChargeDensityStabilityErrorOfLower t.1 N charge (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hz0g : sixVertexContinuationWeightedFiniteDensityGauge ha N ((m + 1) + m) rho z0 < outer)
  (hz1g : sixVertexContinuationWeightedFiniteDensityGauge ha N ((m + 1) + m) rho z1 < outer)
  (hz0 : sixVertexBetheContinuationProjection z0 = ⟨c0, hc0⟩)
  (hz1 : sixVertexBetheContinuationProjection z1 = ⟨c1, hc1⟩)
  (htail : ((((m + 1) + m : Nat) : Real)) < sixVertexAnisotropyMagnitude c0)
  (hbase : sixVertexZeroPhaseBetheEigenvalueValue c0 N z0.1.2 (sixVertexOddCentralIndex m) = sixVertexSectorTopEigenvalue N ((m + 1) + m) (by omega) c0)
  (hwave : sixVertexCoordinateBetheWave (N := N) c0 z0.1.2 ≠ 0) :
-- imply
  sixVertexZeroPhaseBetheEigenvalueValue c1 N z1.1.2 (sixVertexOddCentralIndex m) = sixVertexSectorTopEigenvalue N ((m + 1) + m) (by omega) c1 := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge ha hab hc0 hc1 hc0int hc1int hm hN hcharge rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin z0 z1 hz0g hz1g hz0 hz1 htail hbase hwave


-- created on 2026-10-23
