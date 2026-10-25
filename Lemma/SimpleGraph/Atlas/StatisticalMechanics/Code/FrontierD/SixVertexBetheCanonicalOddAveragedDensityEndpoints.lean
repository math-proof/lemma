import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityEndpoints
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalOddCountingAverage_firstLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddCountingAverage_firstLeft_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1)))) atTop (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddCountingAverage_firstLeft hc s

/--
[sixVertexCanonicalOddRightLast_eq_boundaryZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma sixVertexCanonicalOddRightLast_eq_boundaryZero_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddRightHalfRoot hc s k (Fin.last (s + k)) = sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddRightLast_eq_boundaryZero hc s k

/--
[sixVertexCanonicalOddCountingAverage_boundaryZero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma sixVertexCanonicalOddCountingAverage_boundaryZero_eq_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))) = (((s + k : Nat) : Real) + 3 / 2) / (sixVertexFourWidth (2 * s + 1) k : Real) / sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddCountingAverage_boundaryZero_eq hc s k

/--
[tendsto_sixVertexCanonicalOddBoundaryQuantumRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddBoundaryQuantumRatio_eq
  {s : Nat} :
-- imply
  Tendsto (fun k => (((s + k : Nat) : Real) + 3 / 2) / (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds (1 / 4)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddBoundaryQuantumRatio s

/--
[tendsto_sixVertexCanonicalOddCountingAverage_boundaryZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddCountingAverage_boundaryZero_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)))) atTop (nhds (1 / (4 * Real.pi))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddCountingAverage_boundaryZero hc s

/--
[tendsto_log_sixVertexCanonicalOddCountingAverage_firstLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_log_sixVertexCanonicalOddCountingAverage_firstLeft_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))))) atTop (nhds (Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
-- proof
  apply StatMech.FrontierD.tendsto_log_sixVertexCanonicalOddCountingAverage_firstLeft hc s

/--
[tendsto_log_sixVertexCanonicalOddCountingAverage_boundaryZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_log_sixVertexCanonicalOddCountingAverage_boundaryZero_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))))) atTop (nhds (Real.log (1 / (4 * Real.pi)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_log_sixVertexCanonicalOddCountingAverage_boundaryZero hc s

/--
[tendsto_log_sixVertexCanonicalOddCountingAverage_endpointDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_log_sixVertexCanonicalOddCountingAverage_endpointDifference_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)))) - Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))))) atTop (nhds (Real.log (1 / (4 * Real.pi)) - Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
-- proof
  apply StatMech.FrontierD.tendsto_log_sixVertexCanonicalOddCountingAverage_endpointDifference hc s

/--
[tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => 2 * ∑ j : Fin (s + k + 1), (Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) - Real.log (sixVertexCanonicalOddCountingAverage hc s k (sixVertexCanonicalOddLeftHalfRoot hc s k j)))) atTop (nhds (Real.log (1 / (4 * Real.pi)) - Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement hc s


-- created on 2026-10-23
