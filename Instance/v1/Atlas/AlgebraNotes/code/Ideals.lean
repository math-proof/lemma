/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Ideals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraNotes.code.Ideals


namespace Ideals

instance instCommRingQuotient (R : Type*) [CommRing R] (I : Ideal R) :
    CommRing (R ⧸ I) :=
  Ideal.Quotient.commRing I

end Ideals
