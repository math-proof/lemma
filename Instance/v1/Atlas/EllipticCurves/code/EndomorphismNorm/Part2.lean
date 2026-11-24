module
public import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
public import Def.v1.Atlas.EllipticCurves.code.EndomorphismNorm
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The endomorphism algebra `End⁰(E)` is nontrivial (contains both `0` and `1`). -/
noncomputable instance End0.instNontrivial :
    letI := EndomorphismAlgebra.instRing E; Nontrivial (End0 E) :=
  letI := EndomorphismAlgebra.instRing E
  _root_.WeierstrassCurve.Affine.EndomorphismAlgebra.instNontrivial E

end PositiveDefiniteInvolutionAlgebra
