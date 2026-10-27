import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.MetricSpace.GromovHyperbolic
open Metric


namespace Metric

/--
[isDeltaHyperbolic_zero_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
lemma isDeltaHyperbolic_zero_of_subsingleton
  [PseudoMetricSpace X] [Subsingleton X] :
-- imply
  IsDeltaHyperbolic X 0 := by
-- proof
  refine ⟨le_refl 0, fun w x y z => ?_⟩
  rw [Subsingleton.elim x w, Subsingleton.elim y w, Subsingleton.elim z w, min_self, sub_zero]

end Metric

/--
[IsDeltaHyperbolic.four_point](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
lemma IsDeltaHyperbolic.four_point
  [PseudoMetricSpace X]
  {δ : ℝ}
  {w x y z : X}
-- given
  (h : IsDeltaHyperbolic X δ) :
-- imply
  min (gromovProduct x y w) (gromovProduct y z w) - δ ≤ gromovProduct x z w :=
-- proof
  h.2 w x y z


namespace Metric

/--
[IsDeltaHyperbolic.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
lemma IsDeltaHyperbolic.mono
  [PseudoMetricSpace X]
  {δ δ' : ℝ}
-- given
  (h : IsDeltaHyperbolic X δ)
  (hδ : δ ≤ δ') :
-- imply
  IsDeltaHyperbolic X δ' :=
-- proof
  ⟨h.1.trans hδ, fun w x y z => by
    have := h.four_point w x y z
    linarith⟩

end Metric

namespace Metric

/--
[IsDeltaHyperbolic.nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/GromovHyperbolic.lean)
-/
@[path]
lemma IsDeltaHyperbolic.nonneg
  [PseudoMetricSpace X]
  {δ : ℝ}
-- given
  (h : IsDeltaHyperbolic X δ) :
-- imply
  0 ≤ δ :=
-- proof
  h.1

end Metric


-- created on 2026-10-20
-- updated on 2026-10-26
