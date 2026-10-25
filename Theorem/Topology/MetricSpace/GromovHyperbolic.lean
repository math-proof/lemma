/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean -/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.GromovProduct
import Def.Topology.MetricSpace.GromovHyperbolic
/-!
# Gromov-hyperbolic pseudometric spaces

This file defines Gromov's notion of `δ`-hyperbolicity for a (pseudo)metric space via the
four-point / Gromov-product inequality.

## Main definitions

* `Metric.IsDeltaHyperbolic X δ`: the space `X` is `δ`-hyperbolic, i.e. for all points the Gromov
  product satisfies `(x ∣ z)_w ≥ min (x ∣ y)_w (y ∣ z)_w - δ`, where
  `(x ∣ y)_w = Metric.gromovProduct x y w` (basepoint third, as in Mathlib). The constant
  `δ` is nonnegative by definition.
* `Metric.IsGromovHyperbolic X`: the space `X` is `δ`-hyperbolic for some `δ`.

## Main results

* `Metric.IsDeltaHyperbolic.four_point`: the defining four-point inequality.
* `Metric.IsDeltaHyperbolic.mono`: `δ`-hyperbolicity is monotone in `δ`.
* `Metric.IsDeltaHyperbolic.nonneg`: the constant `δ` is nonnegative.
* `Metric.isDeltaHyperbolic_zero_of_subsingleton`: a subsingleton space is `0`-hyperbolic.

## References

* M. Gromov, *Hyperbolic groups*, in Essays in Group Theory, Math. Sci. Res. Inst. Publ. 8,
  Springer (1987), 75-263. The four-point/Gromov-product formulation of `δ`-hyperbolicity is §1.1.

## Tags

Gromov hyperbolic, hyperbolic metric space, Gromov product
-/


/-! ### Examples -/

-- A single point is `0`-hyperbolic (boundary case `δ = 0`).
example : Metric.IsDeltaHyperbolic (PUnit : Type) 0 :=
  Metric.isDeltaHyperbolic_zero_of_subsingleton

