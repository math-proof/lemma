import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.ScalarCumulantsContinuity
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[tendsto_scalarCumulantsOfMoments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScalarCumulantsContinuity.lean)
-/
@[path]
private lemma tendsto_scalarCumulantsOfMoments_eq
  {moments : Nat → Nat → Real}
  {limitMoments : Nat → Real}
-- given
  (hmoments : ∀ order, Tendsto (fun scale => moments scale order) atTop (nhds (limitMoments order))) :
-- imply
  ∀ order, Tendsto (fun scale => scalarCumulantsOfMoments (moments scale) order) atTop (nhds (scalarCumulantsOfMoments limitMoments order)) := by
-- proof
  apply StatMech.FrontierA.tendsto_scalarCumulantsOfMoments moments limitMoments hmoments


-- created on 2026-10-23
