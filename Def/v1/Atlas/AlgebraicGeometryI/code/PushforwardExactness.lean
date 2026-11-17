/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.Grp.Basic
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PushforwardExactness

@[expose] public section

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
