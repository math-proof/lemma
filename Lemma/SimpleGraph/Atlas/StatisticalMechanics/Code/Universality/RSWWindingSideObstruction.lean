import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWWindingSideObstruction
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_windingSideCounterexample_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_failure_eq :
-- imply
  rlc_windingSideCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_failure

/--
[rlc_windingSideCounterexample_reachSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_reachSet_eq_eq :
-- imply
  rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_reachSet_eq

/--
[rlc_windingSideCounterexample_right_preimages_outside_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_right_preimages_outside_winding_eq
  {x : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1) :
-- imply
  rlc_primalDualReflect.symm x ∉ rlc_outerExitWindingRegion rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_right_preimages_outside_winding hx

/--
[rlc_windingSideCounterexample_not_windingSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_not_windingSplit_eq :
-- imply
  ¬ RlcOuterExitTraceWindingSplit rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_not_windingSplit

/--
[rlc_windingSideCounterexample_not_traceSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_not_traceSeparation_eq :
-- imply
  rlc_windingSideCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧ ¬ RlcOuterExitTraceSeparation rlc_windingSideCounterexampleGap (by norm_num) (by change -1 + 1 < 1; omega) rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_not_traceSeparation


-- created on 2026-10-23
