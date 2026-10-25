/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnApartmentIsoUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Def.v1.Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof.Part2
import Lemma.Fin.LeCard
set_option maxHeartbeats 1600000


namespace GLnBuilding

open scoped Classical

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}


/-- Frame-indexed join: $\mathrm{joinSub}\ F\ S = \bigoplus_{i \in S} F.\mathrm{lines}\ i$. -/
def joinSub (F : Frame k n) (S : Finset (Fin n)) : Submodule k (Vec k n) :=
  ⨆ i ∈ S, F.lines i

end
end GLnBuilding
