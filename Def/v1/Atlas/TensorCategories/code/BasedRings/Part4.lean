/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Structure.v1.Atlas.TensorCategories.code.BasedRings.Part4
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Two normalized 3-cocycles `ω₁, ω₂ : G × G × G → A` are cohomologous if they differ by
the coboundary of some 2-cochain `f : G × G → A`. -/
def CocycleCohomologous {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω₁ ω₂ : NormalizedGroupCocycle3 G A) : Prop :=
  ∃ f : G → G → A,
    ∀ a b c, ω₂.toFun a b c =
      ω₁.toFun a b c * (f b c * (f (a * b) c)⁻¹ * f a (b * c) * (f a b)⁻¹)

end FusionRing
