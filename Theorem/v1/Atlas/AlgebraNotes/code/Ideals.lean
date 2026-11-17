/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Ideals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Def.v1.Atlas.AlgebraNotes.code.Ideals

public section

namespace Ideals

example (R : Type*) [CommRing R] (I : Ideal R) : Prop := Submodule.IsPrincipal I

end Ideals
