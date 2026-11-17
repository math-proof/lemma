/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationYoneda.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Def.v1.Atlas.AlgebraicGeometryI.code.RamificationYoneda
open CategoryTheory Opposite

public section

noncomputable section

namespace Lecture6

example (C : Type*) [Category C] : (yoneda (C := C)).Full := inferInstance

example (C : Type*) [Category C] : (yoneda (C := C)).Faithful := inferInstance

end Lecture6
end
