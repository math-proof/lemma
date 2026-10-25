/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.FiberFunctor
open CategoryTheory MonoidalCategory

universe v u w


namespace TensorCategories

section FiberFunctorAPI

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]

/-- The underlying functor of a fiber functor carries a (lax) monoidal structure. -/
@[reducible]
def FiberFunctor.isMonoidal_1_21 (FF : FiberFunctor k C) : FF.F.Monoidal :=
  FF.monoidal

/-- The tensor structure iso of a fiber functor: `J_{X,Y} : F(X) ⊗ F(Y) ≅ F(X ⊗ Y)`. -/
def FiberFunctor.J_1_21 (FF : FiberFunctor k C) (X Y : C) :
    FF.F.obj X ⊗ FF.F.obj Y ≅ FF.F.obj (X ⊗ Y) :=
  @Functor.Monoidal.μIso _ _ _ _ _ _ FF.F FF.monoidal X Y

/-- The unit isomorphism of a fiber functor: `F(𝟙_ C) ≅ 𝟙_ (ModuleCat k)`. -/
def FiberFunctor.unitIso_1_21 (FF : FiberFunctor k C) :
    FF.F.obj (𝟙_ C) ≅ 𝟙_ (ModuleCat.{w} k) :=
  (@Functor.Monoidal.εIso _ _ _ _ _ _ FF.F FF.monoidal).symm

end FiberFunctorAPI
end TensorCategories
