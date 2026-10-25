/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Abbrev.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
set_option autoImplicit false


namespace HodgeMathlib

/-- The total degree $|\alpha| = \sum_i \alpha_i$ of a multi-index. -/
def multiIndexDegree {n : ℕ} (α : MultiIndex n) : ℕ := α.sum (fun _ k => k)

/-- The monomial $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$ associated to a multi-index. -/
noncomputable def multiIndexMonomial {n : ℕ} (α : MultiIndex n) (ξ : Fin n → ℝ) : ℝ :=
  α.prod (fun i k => (ξ i) ^ k)

/-- The constant multi-index whose every entry equals $k$. -/
noncomputable def constMultiIndex (n : ℕ) (k : ℕ) : MultiIndex n :=
  Finsupp.equivFunOnFinite.symm (fun _ => k)

/-- The finite set of multi-indices componentwise bounded by $(k, \dots, k)$. -/
noncomputable def multiIndicesBounded (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  Finset.Iic (constMultiIndex n k)

/-- The finite set of multi-indices with total degree exactly $k$. -/
noncomputable def multiIndicesOfDegree (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α = k)

/-- The finite set of multi-indices with total degree at most $k$. -/
noncomputable def multiIndicesOfDegreeLE (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α ≤ k)

/-- The principal symbol of a differential operator: $\sigma(L)(\xi) = \sum_{|\alpha| = \mathrm{ord}} a_\alpha \, \xi^\alpha$. -/
noncomputable def principalSymbolDiffForm {n : ℕ} (ord : ℕ)
    (coeff : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1)))
    (ξ : Fin n → ℝ) {k : ℕ} (s : DiffForm n (k + 1)) : DiffForm n (k + 1) :=
  ∑ α ∈ multiIndicesOfDegree n ord, (multiIndexMonomial α ξ) • coeff α s


end HodgeMathlib
