/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.CategoryOII
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import sympy.atlas.v1.Atlas.LieGroups.code.DufloJoseph
import sympy.atlas.v1.Atlas.LieGroups.code.TensorO

noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure RepGfObj (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  carrier : Type u
  inst_addCommGroup : AddCommGroup carrier
  inst_module : Module R carrier
  inst_lieRingModule : LieRingModule 𝔤 carrier
  inst_lieModule : LieModule R 𝔤 carrier

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

opaque IsLocallyFiniteCenterAction {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (_M : RepGfObj R 𝔤) : Prop

structure RepGfHom (M N : RepGfObj R 𝔤) where
  toFun : M.carrier →ₗ⁅R, 𝔤⁆ N.carrier

def RepGfHom.comp {M N P : RepGfObj R 𝔤} (g : RepGfHom N P) (f : RepGfHom M N) :
    RepGfHom M P where
  toFun := g.toFun.comp f.toFun

def RepGfHom.id (M : RepGfObj R 𝔤) : RepGfHom M M where
  toFun := LieModuleHom.id

def RepGfHom.EqAsMap {M N : RepGfObj R 𝔤} (f g : RepGfHom M N) : Prop :=
  ∀ x : M.carrier, f.toFun x = g.toFun x

opaque centerActsNilpotentlyShifted_of_order {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) (n : ℕ) : Prop

def centerActsByScalar_prop {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop :=
  centerActsNilpotentlyShifted_of_order Δ M theta 1

def centerActsNilpotentlyShifted_prop {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ n, centerActsNilpotentlyShifted_of_order Δ M theta n

theorem centerActsByScalar_implies_nilpotentlyShifted {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) :
    centerActsByScalar_prop Δ M theta → centerActsNilpotentlyShifted_prop Δ M theta := by
  intro h
  exact ⟨1, h⟩

structure HasInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_by_scalar : centerActsByScalar_prop Δ M theta

structure HasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_nilpotently_shifted : centerActsNilpotentlyShifted_prop Δ M theta

theorem hasInfChar_implies_hasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R)
    (h : HasInfChar M theta) : HasGenInfChar M theta :=
  ⟨centerActsByScalar_implies_nilpotentlyShifted Δ M theta h.center_acts_by_scalar⟩

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

structure TensorFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  V : Type u
  inst_addCommGroupV : AddCommGroup V
  inst_moduleV : Module R V
  inst_lieRingModuleV : LieRingModule 𝔤 V
  inst_lieModuleV : LieModule R 𝔤 V
  inst_finiteDimV : Module.Finite R V
  inst_freeV : Module.Free R V
  functor : EndoFunctorData R 𝔤
  tensor_obj_spec : ∀ (M : RepGfObj R 𝔤),
    Nonempty ((functor.obj M).carrier ≃ₗ⁅R, 𝔤⁆ (TensorProduct R V M.carrier))
  block_factoring : ∀ (Δ : TriangularDecomposition R 𝔤)
    (theta : Δ.𝔥 →ₗ[R] R) (M : RepGfObj R 𝔤),
    ¬ HasGenInfChar M theta → ∀ (x : (functor.obj M).carrier), x = 0
  is_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (_hex : IsExactSequence f g),
    IsExactSequence (functor.mapHom f) (functor.mapHom g)
  sends_projectives_to_projectives : ∀ (M : RepGfObj R 𝔤),
    IsProjectiveModule M → IsProjectiveModule (functor.obj M)

structure IsProjectiveFunctor (F : EndoFunctorData R 𝔤) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤), IsDirectSummand F FV.functor

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

structure ThetaFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R) where
  baseFunctor : EndoFunctorData R 𝔤
  factors_through_block :
    ∀ (M : RepGfObj R 𝔤), ¬ HasGenInfChar M theta →
    ∀ (x : (baseFunctor.obj M).carrier), x = 0

def AreNatIsoTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  AreNatIso F.baseFunctor G.baseFunctor

def IsDirectSummandTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  IsDirectSummand F.baseFunctor G.baseFunctor

def TensorFunctorData.restrictToTheta (FV : TensorFunctorData R 𝔤)
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R) : ThetaFunctorData R 𝔤 Δ wg theta where
  baseFunctor := FV.functor
  factors_through_block := FV.block_factoring Δ theta

structure IsProjectiveThetaFunctor {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} {theta : Δ.𝔥 →ₗ[R] R}
    (F : ThetaFunctorData R 𝔤 Δ wg theta) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤),
      IsDirectSummandTheta F (FV.restrictToTheta Δ wg theta)

def NatTransThetaSpace {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta) : Type _ :=
  NatTransData F₁.baseFunctor F₂.baseFunctor

def evalAtVerma {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta)
    (Mverma : RepGfObj R 𝔤)
    (eta : NatTransThetaSpace F₁ F₂) :
    RepGfHom (F₁.baseFunctor.obj Mverma) (F₂.baseFunctor.obj Mverma) :=
  eta.app Mverma

structure NatTransOnInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasInfChar M₁ theta)
    (hM₂ : HasInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

structure NatTransOnGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasGenInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasGenInfChar M₁ theta)
    (hM₂ : HasGenInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

def NatTransOnGenInfChar.restrictToInfChar {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (η : NatTransOnGenInfChar theta F₁ F₂) : NatTransOnInfChar theta F₁ F₂ where
  app M hM := η.app M (hasInfChar_implies_hasGenInfChar M theta hM)
  naturality hM₁ hM₂ f :=
    η.naturality (hasInfChar_implies_hasGenInfChar _ theta hM₁)
      (hasInfChar_implies_hasGenInfChar _ theta hM₂) f

def NatTransOnInfChar.EqPointwise {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (α β : NatTransOnInfChar theta F₁ F₂) : Prop :=
  ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta),
    (α.app M hM).EqAsMap (β.app M hM)

def NatTransOnInfChar.comp {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F G H : EndoFunctorData R 𝔤}
    (β : NatTransOnInfChar theta G H) (α : NatTransOnInfChar theta F G) :
    NatTransOnInfChar theta F H where
  app M hM := (β.app M hM).comp (α.app M hM)
  naturality hM₁ hM₂ f x := by
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality hM₁ hM₂ f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality hM₁ hM₂ f ((α.app _ hM₁).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransOnInfChar.id {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F : EndoFunctorData R 𝔤) :
    NatTransOnInfChar theta F F where
  app _ _ := RepGfHom.id _
  naturality _ _ f x := by
    simp [RepGfHom.comp, RepGfHom.id]

def AreNatIsoOnInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransOnInfChar theta F₁ F₂) (β : NatTransOnInfChar theta F₂ F₁),
    (β.comp α).EqPointwise (NatTransOnInfChar.id theta F₁) ∧
    (α.comp β).EqPointwise (NatTransOnInfChar.id theta F₂)

def NatTransOnGenInfChar.comp {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F G H : EndoFunctorData R 𝔤}
    (β : NatTransOnGenInfChar theta G H) (α : NatTransOnGenInfChar theta F G) :
    NatTransOnGenInfChar theta F H where
  app M hM := (β.app M hM).comp (α.app M hM)
  naturality hM₁ hM₂ f x := by
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality hM₁ hM₂ f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality hM₁ hM₂ f ((α.app _ hM₁).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransOnGenInfChar.id {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F : EndoFunctorData R 𝔤) :
    NatTransOnGenInfChar theta F F where
  app _ _ := RepGfHom.id _
  naturality _ _ f x := by
    simp [RepGfHom.comp, RepGfHom.id]

def NatTransOnGenInfChar.EqPointwise {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (α β : NatTransOnGenInfChar theta F₁ F₂) : Prop :=
  ∀ (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta),
    (α.app M hM).EqAsMap (β.app M hM)

def AreNatIsoOnGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransOnGenInfChar theta F₁ F₂) (β : NatTransOnGenInfChar theta F₂ F₁),
    (β.comp α).EqPointwise (NatTransOnGenInfChar.id theta F₁) ∧
    (α.comp β).EqPointwise (NatTransOnGenInfChar.id theta F₂)

def IsDirectSumDecompObj {n : ℕ}
    (M : RepGfObj R 𝔤) (summands : Fin n → RepGfObj R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, RepGfHom (summands i) M)
    (retract_i : ∀ i, RepGfHom M (summands i)),

    (∀ i (x : (summands i).carrier),
      (retract_i i).toFun ((section_i i).toFun x) = x) ∧

    (∀ (x : M.carrier),
      x = Finset.univ.sum (fun i =>
        (section_i i).toFun ((retract_i i).toFun x)))

def IsIndecomposableObj (M : RepGfObj R 𝔤) : Prop :=
  ∀ (e : RepGfHom M M),
    (∀ x, e.toFun (e.toFun x) = e.toFun x) →
    (∀ x, e.toFun x = x) ∨ (∀ x, e.toFun x = 0)

def IsIndecomposable (F : EndoFunctorData R 𝔤) : Prop :=
  ∀ (e : NatTransData F F),
    (e.comp e).EqPointwise e →
    e.EqPointwise (NatTransData.id F) ∨
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier), (e.app M).toFun x = 0)

def IsDirectSumDecomp (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤) : Prop :=

  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),

    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧


    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))

def IsDirectSumDecompGen (F : EndoFunctorData R 𝔤) {ι : Type u} [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),
    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))

def FactorsThroughBlock (Δ : TriangularDecomposition R 𝔤)
    (F : EndoFunctorData R 𝔤) (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (M : RepGfObj R 𝔤),
    ¬ HasGenInfChar M lam →
    ∀ (x : (F.obj M).carrier), x = 0

theorem projective_factors_through_block
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F) :
    FactorsThroughBlock Δ F lam := by


  intro M hM x

  obtain ⟨FV, i, p, hpi⟩ := _hF.exists_tensor_summand

  have hret : (p.app M).toFun ((i.app M).toFun x) = x := by
    have := hpi M x
    simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
               LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq] at this
    exact this

  have hzero : (i.app M).toFun x = (0 : (FV.functor.obj M).carrier) :=
    FV.block_factoring Δ lam M hM ((i.app M).toFun x)

  rw [← hret, hzero, map_zero]

def IsProjectiveFunctor.toThetaFunctorData
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F) :
    ThetaFunctorData R 𝔤 Δ wg lam where
  baseFunctor := F
  factors_through_block := projective_factors_through_block Δ wg lam F hF
