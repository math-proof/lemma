/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/MetricSpace/GromovHyperbolic.lean -/


import Theorem.Topology.MetricSpace.GromovHyperbolic
import Lemma.Set.MetricSpace.GromovHyperbolic


/-- Regression test for the Gromov-product basepoint ordering: from the public
`Metric.IsDeltaHyperbolic ℝ 0` hypothesis, the four-point inequality for the
tree-like configuration with basepoint `0` and points `-R, R, -R` follows
directly through `IsDeltaHyperbolic.four_point`. With the basepoint mistakenly
placed first in the definition, this configuration would force `R ≤ 0`. -/
example (h : Metric.IsDeltaHyperbolic ℝ 0) (R : ℝ) :
    min (Metric.gromovProduct (-R) R (0 : ℝ)) (Metric.gromovProduct R (-R) (0 : ℝ)) - 0 ≤
      Metric.gromovProduct (-R) (-R) (0 : ℝ) :=
  h.four_point 0 (-R) R (-R)

