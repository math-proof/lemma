/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Polynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace Polynomials

abbrev IsPrimitivePolynomial {R : Type*} [CommSemiring R] (p : Polynomial R) : Prop :=
  p.IsPrimitive

end Polynomials
