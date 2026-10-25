/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticParametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Abbrev.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix
open ContinuousLinearMap Finset Manifold


/-- Total degree $|\alpha| = \sum_i \alpha_i$ of a multi-index. -/
def multiIndexDegree {n : ℕ} (α : MultiIndex n) : ℕ :=
  ∑ i : Fin n, α i

/-- The monomial $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$ associated to multi-index $\alpha$. -/
noncomputable def multiIndexMonomial {n : ℕ} (α : MultiIndex n) (ξ : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, (ξ i) ^ (α i)

/-- The finite set of multi-indices $\alpha \in \mathbb{N}^n$ with each component $\alpha_i \le k$. -/
noncomputable def multiIndicesBounded (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  Fintype.piFinset (fun _ : Fin n => Finset.range (k + 1))

/-- The finite set of multi-indices of total degree exactly $k$. -/
noncomputable def multiIndicesOfDegree (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α = k)

/-- The finite set of multi-indices of total degree $\le k$. -/
noncomputable def multiIndicesOfDegreeLE (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α ≤ k)


/-- The principal symbol $\sigma_k(L)(\xi) = \sum_{|\alpha| = k} \xi^\alpha A_\alpha$ of a
differential operator with leading-order coefficients $A_\alpha$. -/
noncomputable def principalSymbol {n : ℕ} {k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : MultiIndex n → (E →L[ℝ] F)) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  ∑ α ∈ multiIndicesOfDegree n k, (multiIndexMonomial α ξ) • (A α)


