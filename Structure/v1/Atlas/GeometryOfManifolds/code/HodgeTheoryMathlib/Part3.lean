/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Interval
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part4
public section

set_option autoImplicit false


namespace HodgeMathlib

/-- Data witnessing that $L$ is a linear differential operator of given order with coefficients $a_\alpha$ and local expression $L = \sum_{|\alpha| \le \mathrm{ord}} a_\alpha \partial^\alpha$. -/
structure IsDifferentialOperator {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  order : ℕ
  coeff : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  coeff_support : ∀ (α : MultiIndex n), multiIndexDegree α > order →
    ∀ {k : ℕ} (ω : DiffForm n (k + 1)), coeff α ω = 0
  partialDeriv : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  local_expression : ∀ {k : ℕ} (s : DiffForm n (k + 1)),
    L s = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff α (partialDeriv α s)
  L_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)), L (α + β) = L α + L β
  L_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)), L (r • α) = r • L α

end HodgeMathlib
