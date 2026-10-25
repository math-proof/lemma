/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzFibrationMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
open Manifold

set_option autoImplicit false


/-- Local model for a Lefschetz singularity: the holomorphic map
$\mathbb{C}^2 \to \mathbb{C},\ (z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
noncomputable def lefschetzLocalModel : ℂ × ℂ → ℂ := fun p => p.1 ^ 2 + p.2 ^ 2


