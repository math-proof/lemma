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
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part2
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
