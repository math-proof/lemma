/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Circle
open Manifold

set_option autoImplicit false


noncomputable section

/-- The intersection form of a 4-manifold: a symmetric bilinear form on $H^2(X;\mathbb{Z})$
described abstractly by its rank $b_2$, the splitting $b_2 = b_2^+ + b_2^-$ into positive
and negative subspaces, signature $\sigma = b_2^+ - b_2^-$, parity (even/odd), and the
explicit bilinear form. -/
structure IntersectionForm where
  b₂ : ℕ
  b₂_plus : ℕ
  b₂_minus : ℕ
  rank_decomp : b₂ = b₂_plus + b₂_minus
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  isEven : Bool
  bilinForm : (Fin b₂ → ℤ) → (Fin b₂ → ℤ) → ℤ

end
