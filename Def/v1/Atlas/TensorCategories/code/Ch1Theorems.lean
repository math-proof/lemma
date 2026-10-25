/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ch1Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctorProjective
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import Class.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective.Part3
import Structure.v1.Atlas.TensorCategories.code.Ch1Theorems
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe u v w u₁ v₁


/-- Theorem 1.35.6 (reconstruction): A finite tensor category `C` equipped with a faithful
additive functor `F : C ⥤ ModuleCat k` can be realized as the representation category of
some `k`-algebra `H`. -/
noncomputable def EGNO.leftQuantumTrace {C : Type v} [Category.{u} C] [MonoidalCategory C]
    [RigidCategory C] {V : C} (a : V ⟶ (Vᘁ)ᘁ) : End (𝟙_ C) :=
  η_ V (Vᘁ) ≫ (a ▷ (Vᘁ)) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- The right quantum trace `Tr^R_V(a)` of a morphism `a : V ⟶ **V` in a rigid monoidal
category, defined via coevaluation, the morphism `a` whiskered on the left by `*V`, and
evaluation. -/
noncomputable def EGNO.rightQuantumTrace {C : Type v} [Category.{u} C] [MonoidalCategory C]
    [RigidCategory C] {V : C} (a : V ⟶ ᘁ(ᘁV)) : End (𝟙_ C) :=
  η_ (ᘁV) V ≫ ((ᘁV : C) ◁ a) ≫ ε_ (ᘁ(ᘁV)) (ᘁV)

/-- Proposition 1.41.1 (part 1): In a semisimple multifusion category, the left dual `*V`
is canonically isomorphic to the right dual `V*`. -/
noncomputable def Prop_1_41_1_leftDual_iso_rightDual
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
    [IsMultifusionCategory C] (V : C) :
    (ᘁV : C) ≅ Vᘁ :=
  prop_1_41_1_leftDualIsoRightDual V

/-- Proposition 1.41.1 (part 2): In a semisimple multifusion category, every object `V` is
canonically isomorphic to its double dual `V**`. -/
noncomputable def Prop_1_41_1_doubleDual_iso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
    [IsMultifusionCategory C] (V : C) :
    V ≅ (Vᘁ)ᘁ :=
  prop_1_41_1_doubleDualIso V

