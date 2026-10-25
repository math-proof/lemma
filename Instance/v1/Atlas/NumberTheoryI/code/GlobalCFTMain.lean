/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFTMain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFTMain


noncomputable section

open NumberField RayClassField

namespace GlobalCFT

universe u

variable (K : Type u) [Field K] [NumberField K]

variable {K}

instance {𝔪 : Modulus K} : CoeOut (CongruenceSubgroup K 𝔪)
    (Subgroup (FracIdealsCoprime K 𝔪)) :=
  ⟨CongruenceSubgroup.toSubgroup⟩

end GlobalCFT
end
