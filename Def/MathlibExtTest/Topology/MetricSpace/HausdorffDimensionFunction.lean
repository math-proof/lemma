/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/MetricSpace/HausdorffDimensionFunction.lean -/


import Instance.Topology.MetricSpace.HausdorffDimensionFunction
import Lemma.Set.MetricSpace.HausdorffDimensionFunction
import Mathlib.Topology.Instances.NNReal.Lemmas
open scoped NNReal Topology
open Filter


/-- Identity gauge as a `HausdorffDimensionFunction`. -/
def idHausdorffDimensionFunction : HausdorffDimensionFunction where
  toContinuousOrderHom := ContinuousOrderHom.id NNReal
  map_zero' := rfl
  map_pos' := fun hr => hr

/-- A dimension function with a plateau, exercising weak rather than strict monotonicity. -/
def cappedHausdorffDimensionFunction : HausdorffDimensionFunction where
  toContinuousOrderHom :=
    { toFun := fun r => min r 1
      monotone' := fun _ _ h => min_le_min h le_rfl
      continuous_toFun := continuous_id.min continuous_const }
  map_zero' := min_eq_left zero_le_one
  map_pos' := fun hr => lt_min hr zero_lt_one

