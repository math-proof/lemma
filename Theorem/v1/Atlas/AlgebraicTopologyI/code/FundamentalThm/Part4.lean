/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part4


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- The defining identity of `liftHomotopyZeroZero`: composing with the differential
`d : Q₁ ⟶ Q₀` recovers `f.f 0`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroZero_comp {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

end Resolution
end FundamentalThm
end
