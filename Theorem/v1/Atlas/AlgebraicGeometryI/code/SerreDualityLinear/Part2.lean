/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part2


namespace SerreDualityP1

open CohomologyP1


/-- The `shiftMap` is involutive, inherited from `residueShift`. -/
theorem shiftMap_involutive (k : Type*) [Field k] :
    Function.Involutive (shiftMap k) := by
  intro f
  show Finsupp.mapDomain residueShift (Finsupp.mapDomain residueShift f) = f
  rw [← Finsupp.mapDomain_comp (f := residueShift) (g := residueShift),
      residueShift_comp_self, Finsupp.mapDomain_id]

end SerreDualityP1
