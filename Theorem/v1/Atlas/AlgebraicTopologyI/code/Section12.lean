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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section12

public section

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The chain group `S_n(X; ℤ)` is definitionally the coproduct of copies of `ℤ`
indexed by singular `n`-simplices, exhibiting it as the free abelian group on
`Sin_n(X)` (Definition 1.3). -/
lemma chainGroup_eq_coprod (X : TopCat.{0}) (n : ℕ) :
    (singularChainFunctorZ.obj X).X n =
    ∐ (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) := rfl

end BarycentricSubdivision
end
