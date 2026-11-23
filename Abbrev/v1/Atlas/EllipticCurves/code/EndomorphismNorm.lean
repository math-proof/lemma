/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
public import Instance.v1.Atlas.EllipticCurves.code.EndomorphismNorm
@[expose] public section

open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The rational endomorphism algebra `End⁰(E) = End(E) ⊗_ℤ ℚ` of an elliptic
curve `E`, an abbreviation for `EndomorphismAlgebra E`. -/
abbrev End0 := EndomorphismAlgebra E

end PositiveDefiniteInvolutionAlgebra
