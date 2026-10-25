/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Module.Projective
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.FundamentalThm
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section22


namespace FundamentalHomologicalAlgebra

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The chain map produced by the **Fundamental Theorem of Homological
Algebra (Theorem 22.1)**: any map `f : Y → Z` between objects of an abelian
category lifts to a chain map between any projective resolution of `Y` and
any resolution of `Z` covering `f`.  See `lift_commutes` for the relation
to the augmentations and `liftUniqueUpToHomotopy` for uniqueness. -/
noncomputable def lift {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    P.complex ⟶ Q.complex :=
  FundamentalThm.lift f P Q

end FundamentalHomologicalAlgebra
