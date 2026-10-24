/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open MeasureTheory MeasurableSpace Set

/-- The vertex of the rectangle `[a, b] ⊆ ℝᵈ` obtained by selecting the lower coordinate
`a i` for indices `i ∈ S` and the upper coordinate `b i` otherwise. Used to compute
inclusion–exclusion sums over all `2^d` vertices. -/
def rectangleVertex {d : ℕ} (a b : Fin d → ℝ) (S : Finset (Fin d)) : Fin d → ℝ :=
  fun i => if i ∈ S then a i else b i

/-- The alternating sum of `F` over the `2^d` vertices of the rectangle `(a, b]`. For a
distribution function `F` on `ℝᵈ`, this equals the mass `μ((a, b])` of the associated
measure (signed inclusion–exclusion). -/
def rectangleValue {d : ℕ} (F : (Fin d → ℝ) → ℝ) (a b : Fin d → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, (-1 : ℝ) ^ S.card * F (rectangleVertex a b S)

/-- `F : ℝᵈ → ℝ` is coordinate-wise non-decreasing: for every coordinate `i`, fixing the
remaining coordinates and increasing the `i`-th argument does not decrease the value of `F`. -/
def IsCoordNonDecreasing {d : ℕ} (F : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin d) (x : Fin d → ℝ) (y z : ℝ), y ≤ z →
    F (Function.update x i y) ≤ F (Function.update x i z)

/-- `F : ℝᵈ → ℝ` is coordinate-wise right continuous: in every coordinate `i`, with the
remaining coordinates fixed, `F` is right-continuous in the `i`-th argument. -/
def IsCoordRightContinuous {d : ℕ} (F : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin d) (x : Fin d → ℝ),
    Filter.Tendsto (fun t => F (Function.update x i t))
      (nhdsWithin (x i) (Ici (x i))) (nhds (F x))

/-- `F` assigns a non-negative inclusion–exclusion value to every rectangle `(a, b]`
with `a ≤ b` coordinate-wise. This is the multivariate analogue of monotonicity of a CDF
and is needed for `F` to come from a measure. -/
def IsRectangleNonneg {d : ℕ} (F : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) → 0 ≤ rectangleValue F a b

namespace MeasureTheory

/-- **Existence (Carathéodory extension)**. Given `F : ℝᵈ → ℝ` that is coordinate-wise
non-decreasing, coordinate-wise right-continuous, and assigns non-negative rectangle values,
there exists a Borel measure `μ` on `ℝᵈ` whose mass on each rectangle `(a, b]` equals
`rectangleValue F a b`. -/
def C_Ioc_pi : Set (Set ℝ) := { S | ∃ l u, l < u ∧ Ioc l u = S }
