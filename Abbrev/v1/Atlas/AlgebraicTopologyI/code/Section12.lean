/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.Colimits


@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The singular chain complex functor with integer coefficients, `X ↦ S_*(X; ℤ)`,
as a functor from topological spaces to non-negatively graded chain complexes of
abelian groups. This is the ambient functor on which the subdivision operator acts. -/
abbrev singularChainFunctorZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

end BarycentricSubdivision
end
