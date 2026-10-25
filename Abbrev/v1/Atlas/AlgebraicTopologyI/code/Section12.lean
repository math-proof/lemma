/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.Colimits


noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The singular chain complex functor with integer coefficients, `X ↦ S_*(X; ℤ)`,
as a functor from topological spaces to non-negatively graded chain complexes of
abelian groups. This is the ambient functor on which the subdivision operator acts. -/
abbrev singularChainFunctorZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

end BarycentricSubdivision
end
