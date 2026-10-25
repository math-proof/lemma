/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Exact
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace DegreeAdditivity

universe u

/-- Grothendieck group `K^0(A) = K^0(R-Mod)` (Def 42, Lec 22): free abelian on iso classes of
modules modulo `[B] = [A] + [C]` for every SES `0 → A → B → C → 0`. -/
abbrev GrothendieckGroupK0 (R : Type u) [Ring R] : Type _ :=
  FreeAbelianGroup (ModuleCat.{u} R) ⧸ K0SESRelSubgroup R

end DegreeAdditivity
end
