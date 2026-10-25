/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Theorem.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part3


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- Degree-zero component of the chain homotopy to zero: if a chain map `f : P → Q` becomes
zero after composing with `Q.π`, lift `f.f 0` along the differential `d : Q₁ ⟶ Q₀` using
exactness of `Q` at degree zero and projectivity of `P.complex.X 0`. -/
def liftHomotopyZeroZero {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

end Resolution
end FundamentalThm
end
