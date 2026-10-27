import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenChargePerronClosed.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedEvenChargeBetheContinuationPoint_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheContinuationPoint_parameter_eq
  {a b c : Real}
  {s k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k).1.1 = c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheContinuationPoint_parameter ha hc s k

/--
[sixVertexFixedEvenChargeBetheContinuationPoint_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheContinuationPoint_roots_eq
  {a b c : Real}
  {s k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k).1.2 = sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc.1) s k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheContinuationPoint_roots ha hc s k

/--
[sixVertexFixedEvenChargeBetheContinuationPoint_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheContinuationPoint_projection_eq
  {a b c : Real}
  {s k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexBetheContinuationProjection (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k) = ⟨c, hc⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheContinuationPoint_projection ha hc s k

/--
[tendsto_sixVertexFixedEvenChargeContinuationGauge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedEvenChargeContinuationGauge_tail_eq
  {a b c : Real}
  {s : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedEvenChargeContinuationGauge_tail ha hc htail s

/--
[sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexFixedEvenChargeBetheEigenvalueValue hc s k = sixVertexLambdaAlongFour c (2 * s) k := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail hc htail s


-- created on 2026-10-23
