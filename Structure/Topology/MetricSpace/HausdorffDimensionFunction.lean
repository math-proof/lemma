/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean -/

import Mathlib.Topology.Order.Hom.Basic
import Mathlib.Topology.UniformSpace.Real
open scoped NNReal Topology
open Filter


/-!
# Hausdorff dimension functions (gauges)

Tushar Das and David Simmons, *Exact dimensions of the prime continued
fraction Cantor set* (arXiv:2305.11829v1), line 211:

> To define these quantities, let ψ:(0,∞) → (0,∞) be a dimension function,
> i.e. a continuous increasing function such that lim_{r→0} ψ(r) = 0.

We extend the source gauge to `NNReal → NNReal` via `ContinuousOrderHom`,
preserving the source codomain on positive radii and the zero limit.
-/

/-- A Hausdorff dimension function (gauge) extending the source
`ψ : (0,∞) → (0,∞)` to `NNReal → NNReal`. Continuous and (weakly) monotone
via `ContinuousOrderHom`, zero at zero, strictly positive at positive
radii; hence `lim_{r→0⁺} ψ r = 0`. -/
structure HausdorffDimensionFunction : Type extends (NNReal →Co NNReal) where
  map_zero' : toFun 0 = 0
  map_pos' : ∀ {r : NNReal}, 0 < r → 0 < toFun r

