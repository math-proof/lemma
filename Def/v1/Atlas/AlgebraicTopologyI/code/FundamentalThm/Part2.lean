/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Instance.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part2


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- The degree-zero component of the lift of `f : Y ⟶ Z` to a chain map between resolutions:
factor `P.π.f 0 ≫ f` through the epi `Q.π.f 0`, using projectivity of `P.complex.X 0`. -/
def liftFZero {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-one component of the lift of `f` to a chain map: use exactness of `Q` at degree
zero together with projectivity of `P.complex.X 1` to lift `d ≫ liftFZero f P Q` along `d`. -/
def liftFOne {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q)
    (by simp [liftFZero])

end Resolution
end FundamentalThm
end
