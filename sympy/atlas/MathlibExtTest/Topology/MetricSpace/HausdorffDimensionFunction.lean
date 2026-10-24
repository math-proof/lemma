/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/MetricSpace/HausdorffDimensionFunction.lean -/


import sympy.atlas.Topology.MetricSpace.HausdorffDimensionFunction
import Lemma.Set.MetricSpace.HausdorffDimensionFunction
import Mathlib.Topology.Instances.NNReal.Lemmas


open scoped NNReal Topology
open Filter

/-- Identity gauge as a `HausdorffDimensionFunction`. -/
def idHausdorffDimensionFunction : HausdorffDimensionFunction where
  toContinuousOrderHom := ContinuousOrderHom.id ℝ≥0
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

-- Exercise all named API lemmas.

example (ψ φ : HausdorffDimensionFunction) (h : ∀ r, ψ r = φ r) : ψ = φ :=
  HausdorffDimensionFunction.ext h

example : Continuous (idHausdorffDimensionFunction : ℝ≥0 → ℝ≥0) :=
  idHausdorffDimensionFunction.continuous

example : Monotone (idHausdorffDimensionFunction : ℝ≥0 → ℝ≥0) :=
  idHausdorffDimensionFunction.monotone

example : ContinuousOrderHomClass HausdorffDimensionFunction ℝ≥0 ℝ≥0 := inferInstance

example : idHausdorffDimensionFunction (0 : ℝ≥0) = 0 :=
  idHausdorffDimensionFunction.map_zero

example {r : ℝ≥0} (hr : 0 < r) : 0 < idHausdorffDimensionFunction r :=
  idHausdorffDimensionFunction.map_pos hr

example {r : ℝ≥0} : idHausdorffDimensionFunction r = 0 ↔ r = 0 :=
  idHausdorffDimensionFunction.map_eq_zero_iff

example : Tendsto (idHausdorffDimensionFunction : ℝ≥0 → ℝ≥0)
    (𝓝[>] (0 : ℝ≥0)) (𝓝 0) :=
  idHausdorffDimensionFunction.tendsto_zero

-- Function coercion evaluates as identity.
example : (idHausdorffDimensionFunction : ℝ≥0 → ℝ≥0) 3 = 3 := rfl

-- Weak monotonicity admits plateaus.
example : cappedHausdorffDimensionFunction 1 = cappedHausdorffDimensionFunction 2 := by
  change min (1 : ℝ≥0) 1 = min 2 1
  norm_num
