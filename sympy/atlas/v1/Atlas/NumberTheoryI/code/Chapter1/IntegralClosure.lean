/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section IntegralElements


abbrev isIntegral_def (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) : Prop := IsIntegral A b

abbrev integralClosureSubalgebra (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    Subalgebra A B := integralClosure A B

end IntegralElements
