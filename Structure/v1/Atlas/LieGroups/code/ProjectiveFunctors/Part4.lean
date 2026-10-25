/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Structure.v1.Atlas.LieGroups.code.TensorO
import Theorem.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part2


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

structure EndoFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  obj : RepGfObj R 𝔤 → RepGfObj R 𝔤
  mapHom : ∀ {M N : RepGfObj R 𝔤}, RepGfHom M N → RepGfHom (obj M) (obj N)
  map_id : ∀ (M : RepGfObj R 𝔤), (mapHom (RepGfHom.id M)).EqAsMap (RepGfHom.id (obj M))
  map_comp : ∀ {M N P : RepGfObj R 𝔤} (f : RepGfHom M N) (g : RepGfHom N P),
    (mapHom (g.comp f)).EqAsMap ((mapHom g).comp (mapHom f))

structure NatTransData (F G : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (G.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (f : RepGfHom M₁ M₂),
    ((app M₂).comp (F.mapHom f)).EqAsMap ((G.mapHom f).comp (app M₁))

end ProjectiveFunctors
end
