/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Grp.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.PushforwardExactness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

universe u v


namespace PushforwardExactness

/-- The pushforward functor on sheaves of abelian groups along a morphism of schemes. -/
noncomputable def schemePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf AddCommGrpCat.{u} (Scheme.forgetToTop.obj X) ⥤
    Sheaf AddCommGrpCat.{u} (Scheme.forgetToTop.obj Y) :=
  Sheaf.pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map f)

/-- The pullback–pushforward adjunction `f⁻¹ ⊣ f_*` for sheaves of abelian groups on
the underlying topological spaces of schemes. -/
noncomputable def schemePullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.pullback AddCommGrpCat.{u} (Scheme.forgetToTop.map f) ⊣ schemePushforward f :=
  Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Scheme.forgetToTop.map f)

end PushforwardExactness
