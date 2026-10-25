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
import Class.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part3
open Manifold

set_option autoImplicit false


noncomputable section

/-- Positive scalar curvature vanishing theorem: if $M$ admits a metric of positive scalar
curvature ($s > 0$), then $\mathrm{SW}(\mathfrak{s}) = 0$ for every Spin-c structure
$\mathfrak{s}$. -/
def s2_cross_s2_intersection_form : IntersectionForm where
  b₂ := 2
  b₂_plus := 1
  b₂_minus := 1
  rank_decomp := rfl
  signature := 0
  signature_eq := by norm_num
  isEven := true
  bilinForm := fun x y => x 0 * y 1 + x 1 * y 0

/-- The intersection form of the $K3$ surface: even of rank 22, with $b_2^+ = 3$, $b_2^- = 19$,
and signature $-16$ (the form $2(-E_8) \oplus 3 H$). -/
def k3_intersection_form : IntersectionForm where
  b₂ := 22
  b₂_plus := 3
  b₂_minus := 19
  rank_decomp := rfl
  signature := -16
  signature_eq := by norm_num
  isEven := true
  bilinForm := fun _ _ => 0


noncomputable section SpinCGroupSection

/-- The element $-1 \in S^1 \subset \mathbb{C}$ regarded as a member of the circle group. -/
def negOneCircle : Circle := ⟨-1, by unfold Submonoid.unitSphere; simp⟩

end SpinCGroupSection
end
