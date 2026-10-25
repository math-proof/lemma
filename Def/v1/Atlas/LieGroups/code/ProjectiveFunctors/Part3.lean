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
import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part4


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

def NatTransData.comp {F G H : EndoFunctorData R 𝔤}
    (β : NatTransData G H) (α : NatTransData F G) : NatTransData F H where
  app M := (β.app M).comp (α.app M)
  naturality f x := by


    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality f ((α.app _).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransData.id (F : EndoFunctorData R 𝔤) : NatTransData F F where
  app _ := RepGfHom.id _
  naturality f x := by

    simp [RepGfHom.comp, RepGfHom.id]

def NatTransData.EqPointwise {F G : EndoFunctorData R 𝔤}
    (α β : NatTransData F G) : Prop :=
  ∀ M : RepGfObj R 𝔤, (α.app M).EqAsMap (β.app M)

def AreNatIso (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransData F G) (β : NatTransData G F),
    (β.comp α).EqPointwise (NatTransData.id F) ∧
    (α.comp β).EqPointwise (NatTransData.id G)

def IsDirectSummand (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (i : NatTransData F G) (p : NatTransData G F),
    (p.comp i).EqPointwise (NatTransData.id F)

def IsExactSequence {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃) : Prop :=
  ∀ (m : M₂.carrier), g.toFun m = 0 ↔ ∃ (x : M₁.carrier), f.toFun x = m

def IsProjectiveModule (M : RepGfObj R 𝔤) : Prop :=
  ∀ {N : RepGfObj R 𝔤} (p : RepGfHom N M),
    (Function.Surjective p.toFun) →
    ∃ (s : RepGfHom M N), (p.comp s).EqAsMap (RepGfHom.id M)

end ProjectiveFunctors
end
