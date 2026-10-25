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
import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part5


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

theorem IsProjectiveFunctor.is_exact {F : EndoFunctorData R 𝔤}
    (hF : IsProjectiveFunctor F)
    {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (_hex : IsExactSequence f g) :
    IsExactSequence (F.mapHom f) (F.mapHom g) := by
  obtain ⟨FV, inc, ret, hRI⟩ := hF.exists_tensor_summand

  have hFVex := FV.is_exact f g _hex

  have inc_nat : ∀ {A B : RepGfObj R 𝔤} (h : RepGfHom A B) (x : (F.obj A).carrier),
      (inc.app B).toFun ((F.mapHom h).toFun x) =
      (FV.functor.mapHom h).toFun ((inc.app A).toFun x) := by
    intro A B h x; exact inc.naturality h x
  have ret_nat : ∀ {A B : RepGfObj R 𝔤} (h : RepGfHom A B) (x : (FV.functor.obj A).carrier),
      (ret.app B).toFun ((FV.functor.mapHom h).toFun x) =
      (F.mapHom h).toFun ((ret.app A).toFun x) := by
    intro A B h x; exact ret.naturality h x
  have hRI' : ∀ M (x : (F.obj M).carrier),
      (ret.app M).toFun ((inc.app M).toFun x) = x := fun M x => hRI M x
  intro m
  constructor
  ·
    intro hgm
    have h1 : (FV.functor.mapHom g).toFun ((inc.app M₂).toFun m) = 0 := by
      rw [← inc_nat g m, hgm, map_zero]
    obtain ⟨y, hy⟩ := (hFVex ((inc.app M₂).toFun m)).mp h1
    refine ⟨(ret.app M₁).toFun y, ?_⟩
    rw [← ret_nat f y, hy, hRI']
  ·
    intro ⟨x, hfx⟩
    have h1 : (inc.app M₃).toFun ((F.mapHom g).toFun m) = 0 := by
      rw [inc_nat g m, ← hfx, inc_nat f x]
      have := ((hFVex ((FV.functor.mapHom f).toFun ((inc.app M₁).toFun x))).mpr
        ⟨(inc.app M₁).toFun x, rfl⟩)
      exact this
    have h2 : (F.mapHom g).toFun m =
        (ret.app M₃).toFun ((inc.app M₃).toFun ((F.mapHom g).toFun m)) :=
      (hRI' M₃ ((F.mapHom g).toFun m)).symm
    rw [h2, h1, map_zero]

theorem IsProjectiveFunctor.sends_projectives_to_projectives {F : EndoFunctorData R 𝔤}
    (hF : IsProjectiveFunctor F)
    (M : RepGfObj R 𝔤)
    (hM : IsProjectiveModule M) : IsProjectiveModule (F.obj M) := by
  obtain ⟨FV, inc, ret, hRI⟩ := hF.exists_tensor_summand

  have hFVM : IsProjectiveModule (FV.functor.obj M) :=
    FV.sends_projectives_to_projectives M hM
  have hRI' : ∀ (x : (F.obj M).carrier),
      (ret.app M).toFun ((inc.app M).toFun x) = x := fun x => hRI M x

  intro N q hq_surj

  letI prodLRM : LieRingModule 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { bracket := fun x mn => (⁅x, mn.1⁆, ⁅x, mn.2⁆)
      add_lie := fun x y mn => by ext <;> exact add_lie x y _
      lie_add := fun x mn₁ mn₂ => by ext <;> exact lie_add x _ _
      leibniz_lie := fun x y mn => by ext <;> exact leibniz_lie x y _ }
  letI prodLM : LieModule R 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { smul_lie := fun r x mn => by ext <;> exact smul_lie r x _
      lie_smul := fun r x mn => by ext <;> exact lie_smul r x _ }
  let pullbackSub : LieSubmodule R 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { carrier := {p | q.toFun p.1 = (ret.app M).toFun p.2}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at *
        rw [ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro r p hp
        simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, map_smul] at *
        rw [hp]
      lie_mem := by
        intro x p hp
        simp only [Set.mem_setOf_eq] at *
        show q.toFun (⁅x, p⁆ : N.carrier × (FV.functor.obj M).carrier).1 = (ret.app M).toFun (⁅x, p⁆ : N.carrier × (FV.functor.obj M).carrier).2
        dsimp [Bracket.bracket, prodLRM]
        rw [LieModuleHom.map_lie q.toFun x p.1, LieModuleHom.map_lie (ret.app M).toFun x p.2, hp] }
  let P : RepGfObj R 𝔤 := ⟨↥pullbackSub, inferInstance, inferInstance, inferInstance, inferInstance⟩

  let π₂ : RepGfHom P (FV.functor.obj M) :=
    ⟨{ toLinearMap := {
         toFun := fun p => p.val.2
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
       map_lie' := fun {x m} => rfl }⟩

  have hπ₂_surj : Function.Surjective π₂.toFun := by
    intro f
    obtain ⟨n, hn⟩ := hq_surj ((ret.app M).toFun f)
    exact ⟨⟨(n, f), hn⟩, rfl⟩

  obtain ⟨σ, hσ⟩ := hFVM π₂ hπ₂_surj

  let π₁ : RepGfHom P N :=
    ⟨{ toLinearMap := {
         toFun := fun p => p.val.1
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
       map_lie' := fun {x m} => rfl }⟩

  let s : RepGfHom (F.obj M) N := π₁.comp (σ.comp (inc.app M))
  refine ⟨s, fun x => ?_⟩
  show (q.comp s).toFun x = (RepGfHom.id (F.obj M)).toFun x
  simp only [s, RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply,
             RepGfHom.id, LieModuleHom.coe_id, id_eq]
  set y := σ.toFun ((inc.app M).toFun x) with hy_def
  have hπ₁_eq : π₁.toFun y = (↑y : N.carrier × (FV.functor.obj M).carrier).1 := rfl
  rw [hπ₁_eq]
  have hpull : q.toFun (↑y : N.carrier × (FV.functor.obj M).carrier).1 =
      (ret.app M).toFun (↑y : N.carrier × (FV.functor.obj M).carrier).2 := y.prop
  have hsec : (↑y : N.carrier × (FV.functor.obj M).carrier).2 = (inc.app M).toFun x := by
    have := hσ ((inc.app M).toFun x)
    exact this
  rw [hpull, hsec, hRI']

end ProjectiveFunctors
end
