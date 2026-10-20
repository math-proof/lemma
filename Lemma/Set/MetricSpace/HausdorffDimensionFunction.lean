import Mathlib
import sympy.Basic
import sympy.atlas.Topology.MetricSpace.HausdorffDimensionFunction
open scoped NNReal Topology
open Filter
open HausdorffDimensionFunction


/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma ext_eq
  {ψ₁ ψ₂ : HausdorffDimensionFunction}
-- given
  (h : ∀ x, ψ₁ x = ψ₂ x) :
-- imply
  ψ₁ = ψ₂ := by
-- proof
  apply HausdorffDimensionFunction.ext h

/--
[continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma continuous_eq
  {ψ : HausdorffDimensionFunction} :
-- imply
  Continuous (ψ : ℝ≥0 → ℝ≥0) := by
-- proof
  apply HausdorffDimensionFunction.continuous ψ

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma monotone_eq
  {ψ : HausdorffDimensionFunction} :
-- imply
  Monotone (ψ : ℝ≥0 → ℝ≥0) := by
-- proof
  apply HausdorffDimensionFunction.monotone ψ

/--
[map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma map_zero_eq
  {ψ : HausdorffDimensionFunction} :
-- imply
  ψ (0 : ℝ≥0) = 0 := by
-- proof
  apply HausdorffDimensionFunction.map_zero ψ

/--
[map_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma map_pos_eq
  {ψ : HausdorffDimensionFunction}
  {r : ℝ≥0}
-- given
  (hr : 0 < r) :
-- imply
  0 < ψ r := by
-- proof
  apply HausdorffDimensionFunction.map_pos ψ hr

/--
[map_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma map_eq_zero_iff_eq
  {ψ : HausdorffDimensionFunction}
  {r : ℝ≥0} :
-- imply
  ψ r = 0 ↔ r = 0 := by
-- proof
  apply HausdorffDimensionFunction.map_eq_zero_iff ψ

/--
[tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean)
-/
@[path]
private lemma tendsto_zero_eq
  {ψ : HausdorffDimensionFunction} :
-- imply
  Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
-- proof
  apply HausdorffDimensionFunction.tendsto_zero ψ


-- created on 2026-10-20
