import Mathlib
import sympy.Basic
import sympy.atlas.Topology.MetricSpace.GromovHyperbolic
open Metric


/--
[IsDeltaHyperbolic.four_point](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
private lemma IsDeltaHyperbolic_four_point_eq
  [PseudoMetricSpace X]
  {δ : ℝ}
  {w x y z : X}
-- given
  (h : IsDeltaHyperbolic X δ) :
-- imply
  min (gromovProduct x y w) (gromovProduct y z w) - δ ≤ gromovProduct x z w := by
-- proof
  apply Metric.IsDeltaHyperbolic.four_point h w x y z

/--
[IsDeltaHyperbolic.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
private lemma IsDeltaHyperbolic_mono_eq
  [PseudoMetricSpace X]
  {δ δ' : ℝ}
-- given
  (h : IsDeltaHyperbolic X δ)
  (hδ : δ ≤ δ') :
-- imply
  IsDeltaHyperbolic X δ' := by
-- proof
  apply Metric.IsDeltaHyperbolic.mono h hδ

/--
[IsDeltaHyperbolic.nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
private lemma IsDeltaHyperbolic_nonneg_eq
  [PseudoMetricSpace X]
  {δ : ℝ}
-- given
  (h : IsDeltaHyperbolic X δ) :
-- imply
  0 ≤ δ := by
-- proof
  apply Metric.IsDeltaHyperbolic.nonneg h

/--
[isDeltaHyperbolic_zero_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
private lemma isDeltaHyperbolic_zero_of_subsingleton_eq
  [PseudoMetricSpace X] [Subsingleton X] :
-- imply
  IsDeltaHyperbolic X 0 := by
-- proof
  apply Metric.isDeltaHyperbolic_zero_of_subsingleton


-- created on 2026-10-20
