import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSwitchingGatePlusPlus
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[plusPlusCurrentSwitchingGate_tendsto_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSwitchingGatePlusPlus.lean)
-/
@[path]
private lemma plusPlusCurrentSwitchingGate_tendsto_unconditional_eq
  {d : Nat}
  {beta : Real}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hd : 1 ≤ d)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => let n := infiniteCurrentBoxSubsequence d beta hbeta k ((plusBoxCurrentMeasure d n beta hbeta).prod (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds (((infinitePlusCurrentMeasure d beta hbeta).prod (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.plusPlusCurrentSwitchingGate_tendsto_unconditional beta hbeta hd hQ x y


-- created on 2026-10-23
