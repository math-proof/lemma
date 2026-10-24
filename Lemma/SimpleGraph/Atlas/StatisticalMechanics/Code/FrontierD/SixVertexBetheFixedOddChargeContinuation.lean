import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedOddChargeBetheParticleCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheParticleCount_eq_eq
  {s k : Nat} :
-- imply
  sixVertexFixedChargeBetheParticleCount (2 * s + 1) k = ((s + k + 1) + 1) + (s + k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheParticleCount_eq s k

/--
[sixVertexFixedOddChargeBetheRoots_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheRoots_mem_open_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexOpenRootSimplex (sixVertexFixedOddChargeBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheRoots_mem_open hc s k

/--
[sixVertexFixedOddChargeBetheRoots_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheRoots_is_solution_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFixedOddChargeBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheRoots_is_solution hc s k

/--
[sixVertexFixedOddChargeBetheContinuationPoint_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheContinuationPoint_projection_eq
  {a b c : Real}
  {s k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexBetheContinuationProjection (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k) = ⟨c, hc⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheContinuationPoint_projection ha hc s k

/--
[sixVertexFiniteRootDensity_fixedOddCharge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_fixedOddCharge_eq_eq
  {c : Real}
  {s k : Nat}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFixedOddChargeBetheRoots hc s k) x = sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_fixedOddCharge_eq hc s k x

/--
[sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq_eq
  {c : Real}
  {s k : Nat}
  {rho : C(Real, Real)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFixedOddChargeBetheRoots hc s k) rho = sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) rho := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq hc s k rho

/--
[tendsto_sixVertexFixedOddChargeContinuationGauge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedOddChargeContinuationGauge_tail_eq
  {a b c : Real}
  {s : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedOddChargeContinuationGauge_tail ha hc htail s


-- created on 2026-10-23
