/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean -/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.GromovProduct
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


namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A pseudometric space `X` is `δ`-hyperbolic (in the sense of Gromov) if `0 ≤ δ` and the
Gromov product satisfies the four-point inequality
`(x ∣ z)_w ≥ min (x ∣ y)_w (y ∣ z)_w - δ` for all points `w x y z`, where
`(x ∣ y)_w = Metric.gromovProduct x y w` (basepoint third, as in Mathlib). -/
def IsDeltaHyperbolic (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∀ w x y z : X, min (gromovProduct x y w) (gromovProduct y z w) - δ ≤ gromovProduct x z w

/-- A pseudometric space is Gromov-hyperbolic if it is `δ`-hyperbolic for some `δ`. -/
def IsGromovHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop := ∃ δ : ℝ, IsDeltaHyperbolic X δ

end Metric
