import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalAxisDecay
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[criticalFreeTwoPoint_axis_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisDecay.lean)
-/
@[path]
private lemma criticalFreeTwoPoint_axis_tendsto_zero_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun r => currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) (criticalAxisSite (by omega) r)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFreeTwoPoint_axis_tendsto_zero hd


-- created on 2026-10-23
