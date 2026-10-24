/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonHolomorphicApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

open Real MeasureTheory

/-- Data of a compact Kähler manifold of complex dimension $n$: an underlying metric/charted space
$M$ with symplectic form $\omega$, almost complex structure $J$ satisfying $J^2 = -\mathrm{id}$,
compatible Riemannian metric $g(v,w) = \omega(v, Jw)$, and a symplectic volume satisfying the
integrality condition $\mathrm{vol} = (2\pi)^n N$ for some $N \in \mathbb{N}_{>0}$. -/
structure CompactKahlerData (n : ℕ) where
  M : Type*
  topM : TopologicalSpace M
  metricM : MetricSpace M
  compactM : CompactSpace M
  nonemptyM : Nonempty M
  chartedM : ChartedSpace (EuclideanSpace ℝ (Fin (2 * n))) M
  ω : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ℝ
  ω_antisymm : ∀ p v w, ω p v w = -(ω p w v)
  J : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ)
  J_sq_neg : ∀ p v, J p (J p v) = fun i => -(v i)
  g : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ℝ
  kahler_compat : ∀ p v w, g p v w = ω p v (J p w)
  symplectic_volume : ℝ
  symplectic_volume_pos : 0 < symplectic_volume
  integrality_condition : ∃ (N : ℕ), 0 < N ∧
    symplectic_volume = (2 * Real.pi) ^ n * ↑N

attribute [instance] CompactKahlerData.topM CompactKahlerData.metricM
  CompactKahlerData.compactM CompactKahlerData.nonemptyM CompactKahlerData.chartedM

/-- A family of complex-valued sections $\sigma_{k,p}(q)$ indexed by $k \in \mathbb{N}$ and
base points $p \in M$, evaluated at $q \in M$. -/
structure SectionFamily {n : ℕ} (D : CompactKahlerData n) where
  section_ : ℕ → D.M → D.M → ℂ

/-- A family of weighted $C^r$ norms $\|\cdot\|_{C^r_k}$ on complex-valued functions on $M$,
scaled according to the parameter $k$ controlling the local length scale $k^{-1/2}$. -/
structure WeightedCrNorm {n : ℕ} (D : CompactKahlerData n) where
  wnorm : ℕ → ℕ → (D.M → ℂ) → ℝ
  wnorm_nonneg : ∀ k r f, 0 ≤ wnorm k r f

/-- An $L^2$ norm $\|\cdot\|_{L^2}$ on complex-valued functions on $M$. -/
structure L2Norm {n : ℕ} (D : CompactKahlerData n) where
  l2 : (D.M → ℂ) → ℝ
  l2_nonneg : ∀ f, 0 ≤ l2 f

/-- The Dolbeault operator $\bar\partial$ acting on complex-valued functions on $M$. -/
structure DelbarOp {n : ℕ} (D : CompactKahlerData n) where
  delbar : (D.M → ℂ) → (D.M → ℂ)
