/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonApproxHolomorphic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
set_option autoImplicit false


namespace Donaldson

noncomputable section

open Real


/-- Data for a compact Kähler manifold: a metric space $M$, complex dimension $n$, a
non-degenerate antisymmetric 2-form $\omega$, an almost complex structure $J$ with $J^2 = -I$,
the Kähler metric $g(v,w) = \omega(v, J w)$, and an integrality condition on the symplectic
volume (needed for Donaldson's pre-quantization). -/
structure CompactKahlerData where
  M : Type*
  metricInst : MetricSpace M
  compactInst : @CompactSpace M metricInst.toUniformSpace.toTopologicalSpace
  complexDim : ℕ
  dim_pos : 0 < complexDim
  ω : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  ω_antisymm : ∀ p v w, ω p v w = -(ω p w v)
  J : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ)
  J_sq_neg : ∀ p v, J p (J p v) = fun i => -(v i)
  g : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  kahler_compat : ∀ p v w, g p v w = ω p v (J p w)
  symplectic_volume : ℝ
  symplectic_volume_pos : 0 < symplectic_volume
  integrality_condition : ∃ (N : ℕ), 0 < N ∧
    symplectic_volume = (2 * Real.pi) ^ complexDim * ↑N

/-- A family $\{\sigma_{k,p}\}$ of sections indexed by an integer $k$ and a basepoint $p \in M$. -/
structure SectionFamily (X : CompactKahlerData) where
  section_ : ℕ → X.M → X.M → ℂ

/-- Abstraction of the $k$-weighted $C^r$ sup-norm $\sup_x (k^{r/2}|\nabla^r s(x)|)$, with the
basic properties (non-negativity, neg-invariance, and pointwise control for $r=0$). -/
structure WeightedSupNorm (X : CompactKahlerData) where
  eval : ℕ → ℕ → (X.M → ℂ) → ℝ
  nonneg : ∀ k r s, 0 ≤ eval k r s
  neg_le : ∀ k r s, eval k r (fun x => -(s x)) ≤ eval k r s
  pointwise_control : ∀ k s (B : ℝ), 0 ≤ B → (∀ x : X.M, ‖s x‖ ≤ B) → eval k 0 s ≤ B

/-- Abstraction of an $L^2$ norm on sections, with the basic property of non-negativity. -/
structure L2Norm (X : CompactKahlerData) where
  norm : (X.M → ℂ) → ℝ
  nonneg : ∀ s, 0 ≤ norm s

/-- Abstraction of the Dolbeault operator $\bar\partial$ on sections of $L^k$, together with the
pointwise estimate that $|\bar\partial$ applied to the Gaussian peak section$|\leq C/\sqrt k$. -/
structure DelbarOp (X : CompactKahlerData) where
  delbar : (X.M → ℂ) → (X.M → ℂ)
  delbar_gaussian_pointwise_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, ∀ p x : X.M,
      ‖delbar (fun q => (Real.exp (-(↑k : ℝ) *
        (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ)) x‖ ≤
        C / Real.sqrt (↑k)


end
end Donaldson
