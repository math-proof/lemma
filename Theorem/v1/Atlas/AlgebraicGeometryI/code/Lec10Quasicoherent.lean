/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10Quasicoherent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec10Quasicoherent


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

example (R : CommRingCat.{0}) (M : ModuleCat.{0} R) :
    IsQuasicoherent_Def24 (tilde M) :=
  inferInstance

end
