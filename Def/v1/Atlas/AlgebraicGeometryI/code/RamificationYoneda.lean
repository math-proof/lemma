/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationYoneda.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
open CategoryTheory Opposite


noncomputable section

namespace Lecture6

/-- The Yoneda embedding `C → [Cᵒᵖ, Type]` is fully faithful, the categorical
input behind functor-of-points reasoning in ramification arguments. -/
def yonedaFullyFaithful (C : Type*) [Category C] :
    (yoneda (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

end Lecture6
end
