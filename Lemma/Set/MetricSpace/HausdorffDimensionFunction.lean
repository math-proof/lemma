import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Topology.MetricSpace.HausdorffDimensionFunction
open scoped NNReal Topology
open Filter
open HausdorffDimensionFunction


namespace HausdorffDimensionFunction

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma ext
  {ψ₁ ψ₂ : HausdorffDimensionFunction}
-- given
  (h : ∀ x, ψ₁ x = ψ₂ x) :
-- imply
  ψ₁ = ψ₂ :=
-- proof
  DFunLike.ext ψ₁ ψ₂ h

end HausdorffDimensionFunction

/--
[continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma continuous
  {ψ : HausdorffDimensionFunction} :
-- imply
  Continuous (ψ : ℝ≥0 → ℝ≥0) :=
-- proof
  ψ.toContinuousOrderHom.continuous_toFun


namespace HausdorffDimensionFunction

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma monotone
  {ψ : HausdorffDimensionFunction} :
-- imply
  Monotone (ψ : ℝ≥0 → ℝ≥0) :=
-- proof
  ψ.toContinuousOrderHom.monotone

end HausdorffDimensionFunction

namespace HausdorffDimensionFunction

/--
[map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma map_zero
  {ψ : HausdorffDimensionFunction} :
-- imply
  ψ (0 : ℝ≥0) = 0 :=
-- proof
  ψ.map_zero'

end HausdorffDimensionFunction

namespace HausdorffDimensionFunction

/--
[map_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma map_pos
  {ψ : HausdorffDimensionFunction}
  {r : ℝ≥0}
-- given
  (hr : 0 < r) :
-- imply
  0 < ψ r :=
-- proof
  ψ.map_pos' hr

end HausdorffDimensionFunction

namespace HausdorffDimensionFunction

/--
[map_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma map_eq_zero_iff
  {ψ : HausdorffDimensionFunction}
  {r : ℝ≥0} :
-- imply
  ψ r = 0 ↔ r = 0 := by
-- proof
  constructor
  · intro h
    by_contra hr
    have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
    have hpos : 0 < ψ r := ψ.map_pos hrpos
    exact ne_of_gt hpos h
  · rintro rfl
    exact ψ.map_zero

end HausdorffDimensionFunction

namespace HausdorffDimensionFunction

/--
[tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
lemma tendsto_zero
  {ψ : HausdorffDimensionFunction} :
-- imply
  Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
-- proof
  have h : Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝 (0 : ℝ≥0)) (𝓝 (ψ (0 : ℝ≥0))) :=
    ψ.continuous.continuousAt
  rw [ψ.map_zero] at h
  exact h.mono_left inf_le_left

end HausdorffDimensionFunction


-- created on 2026-10-20
-- updated on 2026-10-26
