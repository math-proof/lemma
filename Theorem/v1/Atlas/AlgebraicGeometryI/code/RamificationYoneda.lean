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
import Def.v1.Atlas.AlgebraicGeometryI.code.RamificationYoneda
open CategoryTheory Opposite


noncomputable section

namespace Lecture6

example (C : Type*) [Category C] : (yoneda (C := C)).Full := inferInstance

example (C : Type*) [Category C] : (yoneda (C := C)).Faithful := inferInstance

end Lecture6
end
