/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.Twists
import Lemma.Category.Atlas.v1.TensorCategories.code.Twists

open CategoryTheory TensorCategories

universe u

section Prop_1_36_5

variable (k : Type u) [Field k] (G : Type u) [Group G]

/-- Map from `H^2(G, k×)` to isomorphism classes of monoidal fiber functors on `Vec_G`,
sending a cohomology class `[J]` to the isomorphism class of the fiber functor twisted by
the cocycle `J`. -/
noncomputable def cocycleH2ToFiberFunctorClass :
    CocycleH2 G kˣ → MonoidalFiberFunctorIsoClasses k (VecG k G) :=
  Quotient.lift
    (fun J => @Quotient.mk _ (monoidalFiberFunctorSetoid k (VecG k G))
      (cocycleToFiberFunctor k G J))
    (fun J₁ J₂ h => Quotient.sound
      ((cocycleToFiberFunctor_iso_iff_cohomologous k G J₁ J₂).mpr h))
