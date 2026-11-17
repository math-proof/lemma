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
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section12

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The barycenter of the standard `n`-simplex `Δ^n`: the point all of whose
barycentric coordinates equal `1/(n+1)`. This is the cone point used in the
subdivision construction of Section 12. -/
def barycenter (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun _ => 1 / (n + 1 : ℝ), by
    constructor
    · intro i; positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring⟩

/-- The standard topological `n`-simplex `Δ^n`, viewed as an object of `TopCat`. -/
def stdSimplexTop (n : ℕ) : TopCat.{0} :=
  SimplexCategory.toTop.{0}.obj (SimplexCategory.mk n)

/-- The type of singular `n`-simplices of `X`, i.e. `Sin_n(X)`, accessed via the
underlying simplicial set of `X`. -/
def SingType (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.{0}.obj X).obj (Opposite.op (SimplexCategory.mk n))

end BarycentricSubdivision
end
