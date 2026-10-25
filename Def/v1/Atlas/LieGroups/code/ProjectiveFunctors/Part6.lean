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
import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part8


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

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

end ProjectiveFunctors
end
