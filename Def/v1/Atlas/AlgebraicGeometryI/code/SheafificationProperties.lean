/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u


namespace Proposition15

/-- The sheafification adjunction: presheafification ⊣ inclusion of sheaves into
presheaves, instantiated for abelian-group-valued (pre)sheaves on a topological
space `X`. -/
noncomputable def sheafification_adjunction (X : TopCat.{u}) :
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⊣
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}

end Proposition15
