/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 400000

open MeasureTheory Real BigOperators Finset ENNReal Set

namespace TSPConcentration

/-- A point in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The length $L_n$ of the optimal Travelling Salesman tour through the
$n$ points $\mathit{points}_0, \dots, \mathit{points}_{n-1}$: the infimum over
permutations $σ$ of the total cyclic distance
$\sum_i \mathrm{dist}(\mathit{points}_{σ(i)}, \mathit{points}_{σ(i+1 \bmod n)})$.
Returns $0$ when $n = 0$. -/
noncomputable def tspTourLength (n : ℕ) (points : Fin n → Point) : ℝ :=
  if h : n = 0 then 0
  else ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    dist (points (σ i)) (points (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩))

/-- The random variable $X$ is $K$-sub-Gaussian about its mean under $μ$:
for every $t \geq 0$,
$μ(\{ω : |X(ω) - \mathbb{E}_μ X| \geq t\}) \leq 2 e^{-t^2 / K^2}$. -/
def IsSubGaussianAboutMean {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (K : ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤
      ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))
