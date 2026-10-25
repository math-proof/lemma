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
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_36_4.Part3
open scoped TensorProduct
open CategoryTheory

universe u


section Prop1364FiberFunctorClasses

open TensorCategories

universe v w

/-- Setoid on `FiberFunctor k C` given by monoidal isomorphism. -/
noncomputable def Prop1364.fiberFunctorSetoid
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :
    Setoid (FiberFunctor k C) where
  r := Prop1364.FiberFunctorMonoidalIsomorphic
  iseqv := Prop1364.FiberFunctorMonoidalIsomorphic.equivalence

/-- The set of monoidal isomorphism classes of fiber functors on `C`. -/
def Prop1364.FiberFunctorIsoClasses
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :=
  Quotient (Prop1364.fiberFunctorSetoid k C)

end Prop1364FiberFunctorClasses
