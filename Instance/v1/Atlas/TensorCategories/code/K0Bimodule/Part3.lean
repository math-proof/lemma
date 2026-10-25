/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite
import Def.v1.Atlas.TensorCategories.code.K0Bimodule
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Left action of the Grothendieck ring `Gr(R)` on `K₀(R)` via `k0ActLeft`. -/
instance instSMulLeft : SMul (GrRingOf R) (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActLeft r.coeff m.coeff⟩⟩

end FusionRing
