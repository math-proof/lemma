import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPrefactorLimit
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedOddChargeBethePrefactor_log_div_width_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddPrefactorLimit.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBethePrefactor_log_div_width_tendsto_zero_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  Tendsto (fun k : Nat ↦ Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k)) / (sixVertexFourWidth r k : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBethePrefactor_log_div_width_tendsto_zero hc hr


-- created on 2026-10-23
