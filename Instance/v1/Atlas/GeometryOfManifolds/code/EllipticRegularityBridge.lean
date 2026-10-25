/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge
set_option autoImplicit false


namespace EllipticRegularityBridge

/-- Pointwise additive group structure on differential $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on differential $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

/-- Borel measurable space structure on $\mathbb{R}^n$, needed for integration of forms. -/
noncomputable instance instMeasurableSpace (n : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

end EllipticRegularityBridge
