/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFTMain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import Instance.v1.Atlas.NumberTheoryI.code.GlobalCFTMain


noncomputable section

open NumberField RayClassField

namespace GlobalCFT

universe u

variable (K : Type u) [Field K] [NumberField K]

variable {K}

def CongruenceSubgroup.ray (𝔪 : Modulus K) : CongruenceSubgroup K 𝔪 :=
  ⟨RayGroup K 𝔪, le_refl _⟩

def CongruenceSubgroup.top (𝔪 : Modulus K) : CongruenceSubgroup K 𝔪 :=
  ⟨⊤, le_top⟩

def CongruenceSubgroup.index {𝔪 : Modulus K} (𝒞 : CongruenceSubgroup K 𝔪) : ℕ :=
  𝒞.toSubgroup.index

end GlobalCFT
end
