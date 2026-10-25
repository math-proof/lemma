/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
import Theorem.v1.Atlas.EllipticCurves.code.EndomorphismNorm
open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- A nontrivial PD-involution algebra has no zero divisors. -/
instance instNoZeroDivisors [Nontrivial A] : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := eq_zero_or_eq_zero_of_mul_eq_zero a b hab

/-- A nontrivial PD-involution algebra is an integral domain. -/
instance instIsDomain [Nontrivial A] : IsDomain A :=
  NoZeroDivisors.to_isDomain A

end PositiveDefiniteInvolutionAlgebra
