/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/MetricSpace/HausdorffDimensionFunction.lean -/


import Instance.Topology.MetricSpace.HausdorffDimensionFunction
import Lemma.Set.MetricSpace.HausdorffDimensionFunction
import Mathlib.Topology.Instances.NNReal.Lemmas
import Def.MathlibExtTest.Topology.MetricSpace.HausdorffDimensionFunction
open scoped NNReal Topology
open Filter


-- Exercise all named API lemmas.

example (ψ φ : HausdorffDimensionFunction) (h : ∀ r, ψ r = φ r) : ψ = φ :=
  HausdorffDimensionFunction.ext h

example : Continuous (idHausdorffDimensionFunction : NNReal → NNReal) :=
  idHausdorffDimensionFunction.continuous

example : Monotone (idHausdorffDimensionFunction : NNReal → NNReal) :=
  idHausdorffDimensionFunction.monotone

example : ContinuousOrderHomClass HausdorffDimensionFunction NNReal NNReal := inferInstance

example : idHausdorffDimensionFunction (0 : NNReal) = 0 :=
  idHausdorffDimensionFunction.map_zero

example {r : NNReal} (hr : 0 < r) : 0 < idHausdorffDimensionFunction r :=
  idHausdorffDimensionFunction.map_pos hr

example {r : NNReal} : idHausdorffDimensionFunction r = 0 ↔ r = 0 :=
  idHausdorffDimensionFunction.map_eq_zero_iff

example : Tendsto (idHausdorffDimensionFunction : NNReal → NNReal)
    (𝓝[>] (0 : NNReal)) (𝓝 0) :=
  idHausdorffDimensionFunction.tendsto_zero

-- Function coercion evaluates as identity.
example : (idHausdorffDimensionFunction : NNReal → NNReal) 3 = 3 := rfl

-- Weak monotonicity admits plateaus.
example : cappedHausdorffDimensionFunction 1 = cappedHausdorffDimensionFunction 2 := by
  change min (1 : NNReal) 1 = min 2 1
  norm_num

