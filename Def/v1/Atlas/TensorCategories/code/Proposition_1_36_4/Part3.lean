/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_36_4.Part2
open scoped TensorProduct
open CategoryTheory

universe u


section Prop1364GaugeEquiv

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- The setoid on `BialgebraTwist R H` given by gauge equivalence. -/
noncomputable def Prop1364.gaugeEquivSetoid :
    Setoid (Prop1364.BialgebraTwist R H) where
  r T₁ T₂ := Prop1364.GaugeEquiv T₁.J T₂.J
  iseqv := {
    refl := fun T => Prop1364.GaugeEquiv.refl T.J
    symm := fun h => Prop1364.GaugeEquiv.symm h
    trans := fun h₁ h₂ => Prop1364.GaugeEquiv.trans h₁ h₂
  }

/-- The set of gauge equivalence classes of bialgebra twists on `H`. -/
def Prop1364.BialgebraTwistClasses :=
  Quotient (Prop1364.gaugeEquivSetoid R H)

end Prop1364Classes


section Prop1364FiberFunctorClasses

open TensorCategories

universe v w

/-- Two fiber functors are monoidally isomorphic if there exists a natural isomorphism
between their underlying functors which is also a monoidal natural transformation. -/
def Prop1364.FiberFunctorMonoidalIsomorphic
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF₁ FF₂ : FiberFunctor k C) : Prop :=
  ∃ (α : FF₁.F ≅ FF₂.F),
    @NatTrans.IsMonoidal C _ _ (ModuleCat k) _ _ FF₁.F FF₂.F α.hom
      FF₁.monoidal.toLaxMonoidal FF₂.monoidal.toLaxMonoidal

end Prop1364FiberFunctorClasses
