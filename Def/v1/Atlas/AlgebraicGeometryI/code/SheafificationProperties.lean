/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
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
