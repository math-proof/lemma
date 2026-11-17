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
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part2
public section

set_option autoImplicit false


namespace HodgeMathlib

/-- A codifferential operator $d^* : \Omega^{k+1} \to \Omega^k$ that is linear and satisfies $d^* \circ d^* = 0$. -/
structure Codifferential (n : ℕ) where
  dstar : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n k
  dstar_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)),
    dstar (α + β) = dstar α + dstar β
  dstar_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)),
    dstar (r • α) = r • dstar α
  dstar_squared : ∀ {k : ℕ} (ω : DiffForm n (k + 2)), dstar (dstar ω) = 0


end HodgeMathlib
