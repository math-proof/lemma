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

We extend the source gauge to `ℝ≥0 → ℝ≥0` via `ContinuousOrderHom`,
preserving the source codomain on positive radii and the zero limit.
-/

/-- A Hausdorff dimension function (gauge) extending the source
`ψ : (0,∞) → (0,∞)` to `ℝ≥0 → ℝ≥0`. Continuous and (weakly) monotone
via `ContinuousOrderHom`, zero at zero, strictly positive at positive
radii; hence `lim_{r→0⁺} ψ r = 0`. -/
structure HausdorffDimensionFunction : Type extends (ℝ≥0 →Co ℝ≥0) where
  map_zero' : toFun 0 = 0
  map_pos' : ∀ {r : ℝ≥0}, 0 < r → 0 < toFun r

instance : FunLike HausdorffDimensionFunction ℝ≥0 ℝ≥0 where
  coe ψ := ψ.toContinuousOrderHom
  coe_injective ψ φ h := by
    cases ψ
    cases φ
    simp only [HausdorffDimensionFunction.mk.injEq]
    exact ContinuousOrderHom.ext fun r ↦ congrFun h r

instance : ContinuousOrderHomClass HausdorffDimensionFunction ℝ≥0 ℝ≥0 where
  map_monotone ψ := ψ.toContinuousOrderHom.monotone
  map_continuous ψ := ψ.toContinuousOrderHom.continuous_toFun

namespace HausdorffDimensionFunction

@[ext]
theorem ext {ψ₁ ψ₂ : HausdorffDimensionFunction} (h : ∀ x, ψ₁ x = ψ₂ x) : ψ₁ = ψ₂ :=
  DFunLike.ext ψ₁ ψ₂ h

/-- Continuity as a function `ℝ≥0 → ℝ≥0`. -/
theorem continuous (ψ : HausdorffDimensionFunction) : Continuous (ψ : ℝ≥0 → ℝ≥0) :=
  ψ.toContinuousOrderHom.continuous_toFun

/-- Weak monotonicity inherited from `ContinuousOrderHom`. -/
theorem monotone (ψ : HausdorffDimensionFunction) : Monotone (ψ : ℝ≥0 → ℝ≥0) :=
  ψ.toContinuousOrderHom.monotone

/-- Value at zero. -/
@[simp]
theorem map_zero (ψ : HausdorffDimensionFunction) : ψ (0 : ℝ≥0) = 0 :=
  ψ.map_zero'

/-- Strict positivity at positive radii, preserving source codomain `(0,∞)`. -/
theorem map_pos (ψ : HausdorffDimensionFunction) {r : ℝ≥0} (hr : 0 < r) : 0 < ψ r :=
  ψ.map_pos' hr

/-- Vanishing exactly at zero: `ψ r = 0 ↔ r = 0`. -/
theorem map_eq_zero_iff (ψ : HausdorffDimensionFunction) {r : ℝ≥0} : ψ r = 0 ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
    have hpos : 0 < ψ r := ψ.map_pos hrpos
    exact ne_of_gt hpos h
  · rintro rfl
    exact ψ.map_zero

/-- Source limit `lim_{r→0} ψ r = 0`, realized as `Tendsto ψ (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_zero (ψ : HausdorffDimensionFunction) :
    Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have h : Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝 (0 : ℝ≥0)) (𝓝 (ψ (0 : ℝ≥0))) :=
    ψ.continuous.continuousAt
  rw [ψ.map_zero] at h
  exact h.mono_left inf_le_left

end HausdorffDimensionFunction
