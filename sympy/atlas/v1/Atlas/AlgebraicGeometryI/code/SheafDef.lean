/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
  TopologicalSpace TopologicalSpace.Opens Opposite

universe x

namespace TopCat.Presheaf

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {X : TopCat.{x}} (F : Presheaf C X)

/-- **Gluing axiom**: every compatible family `(sᵢ ∈ F(Uᵢ))` of local sections
admits a section on the union `⋃ Uᵢ` whose restrictions agree with `sᵢ`. -/
def SatisfiesGluing : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X) (sf : ∀ i, ToType (F.obj (op (U i)))),
    F.IsCompatible U sf → ∃ s : ToType (F.obj (op (iSup U))), F.IsGluing U sf s

/-- **Locality axiom**: two sections of `F` over `⋃ Uᵢ` that agree on every `Uᵢ`
are equal. -/
def SatisfiesLocality : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X)
    (s t : ToType (F.obj (op (iSup U)))),
    (∀ i, F.map (Opens.leSupr U i).op s = F.map (Opens.leSupr U i).op t) → s = t
