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
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnApartmentIsoUnconditional
set_option maxHeartbeats 1600000


namespace GLnBuilding

open scoped Classical

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}


/-- The map $S \mapsto \mathrm{joinSub}\ F\ S$ is injective. -/
theorem joinSub_injective (F : Frame k n) : Function.Injective (joinSub F) := by
  intro S₁ S₂ h; by_contra hne; exact frame_biSup_injective k n F hne h

/-- Every `joinSub F S` is $F$-compatible by definition. -/
theorem joinSub_isCompatible (F : Frame k n) (S : Finset (Fin n)) :
    F.IsCompatible k n (joinSub F S) := ⟨S, rfl⟩

/-- Round-trip identity: `extractFinset F (joinSub F S) = S`. -/
theorem extractFinset_of_joinSub (F : Frame k n) (S : Finset (Fin n)) :
    extractFinset k n F (joinSub F S) = S := by
  have hcompat : F.IsCompatible k n (joinSub F S) := joinSub_isCompatible F S
  have hspec := extractFinset_spec k n F (joinSub F S) hcompat
  have : joinSub F (extractFinset k n F (joinSub F S)) = joinSub F S := hspec.symm
  exact joinSub_injective F this

/-- Round-trip identity: `joinSub F (extractFinset F V) = V` for any $F$-compatible $V$. -/
theorem joinSub_extractFinset (F : Frame k n) (V : Submodule k (Vec k n))
    (h : F.IsCompatible k n V) : joinSub F (extractFinset k n F V) = V :=
  (extractFinset_spec k n F V h).symm


end
end GLnBuilding
