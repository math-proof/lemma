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
import Structure.v1.Atlas.GeometryOfManifolds.code.DonaldsonApproxHolomorphic
set_option autoImplicit false


namespace Donaldson

noncomputable section

open Real


variable {X : CompactKahlerData}

/-- The family $\{\sigma_{k,p}\}$ is uniformly $C^r$-bounded for every $r$. -/
def IsUniformlyBounded (wdn : WeightedSupNorm X) (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (fam.section_ k p) ≤ C_r

/-- The family is approximately holomorphic: $\|\bar\partial \sigma_{k,p}\|_{C^r} \leq C_r/\sqrt{k}$. -/
def IsApproxHolomorphic (wdn : WeightedSupNorm X) (dol : DelbarOp X)
    (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (dol.delbar (fam.section_ k p)) ≤
      C_r / Real.sqrt (↑k)

/-- The family is uniformly Gaussian-concentrated around $p$:
$|\sigma_{k,p}(x)| \leq C \exp(-\lambda k\, d(p,x)^2)$. -/
def IsUniformlyConcentrated (fam : SectionFamily X) : Prop :=
  ∃ C lam : ℝ, C > 0 ∧ lam > 0 ∧
    ∀ k : ℕ, ∀ p x : X.M, ‖fam.section_ k p x‖ ≤
      C * Real.exp (-lam * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2)

/-- A family is truly holomorphic if $\bar\partial \sigma_{k,p} = 0$ for all $k, p$. -/
def IsHolomorphicFamily (dol : DelbarOp X) (fam : SectionFamily X) : Prop :=
  ∀ k : ℕ, ∀ p : X.M, dol.delbar (fam.section_ k p) = 0

/-- Two families are exponentially close in every $C^r$-norm:
$\|\sigma_{k,p} - \tilde\sigma_{k,p}\|_{C^r} \leq C_r \exp(-\lambda k^{1/3})$. -/
def IsExponentiallyClose (wdn : WeightedSupNorm X)
    (fam fam' : SectionFamily X) : Prop :=
  ∃ lam : ℝ, lam > 0 ∧
    ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ p : X.M,
        wdn.eval k r (fun x => fam.section_ k p x - fam'.section_ k p x) ≤
          C_r * Real.exp (-lam * (↑k) ^ ((1 : ℝ) / 3))


/-- The Gaussian peak section family $\sigma_{k,p}(q) = e^{-k\, d(p,q)^2/4}$ used as a model
for Donaldson's near-holomorphic peak sections. -/
def gaussianPeakSection (X : CompactKahlerData) : SectionFamily X :=
  { section_ := fun k p q =>
      (Real.exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ) }

end
end Donaldson
