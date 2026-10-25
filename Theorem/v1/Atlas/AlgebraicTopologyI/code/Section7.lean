/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section7.Part2
open ExactSequence


namespace HomologyCrossProduct

section SingularIntComplexConstruction

open AlgebraicTopologyI

/-- Technical cast lemma: rewriting an additive map `SingularChains (m+1) X →+
SingularChains m X` along equalities of natural-number indices behaves like
casting the input and output through the corresponding equalities on the
chain groups. -/
lemma hom_cast_apply_singular (X : Type) [TopologicalSpace X]
    (m n k : ℕ) (h1 : m + 1 = n) (h2 : m = k)
    (f : SingularChains (m + 1) X →+ SingularChains m X)
    (x : SingularChains n X) :
    (h1 ▸ h2 ▸ f : SingularChains n X →+ SingularChains k X) x =
      cast (congrArg (SingularChains · X) h2) (f (cast (congrArg (SingularChains · X) h1.symm) x)) := by
  subst h1; subst h2; simp

/-- Casting a chain along an equality of degrees gives zero iff the original
chain was zero. -/
lemma cast_singularChains_eq_zero (X : Type) [TopologicalSpace X]
    {m n : ℕ} (h : m = n) (x : SingularChains m X) :
    cast (congrArg (SingularChains · X) h) x = (0 : SingularChains n X) ↔ x = 0 := by
  subst h; simp

/-- Compatibility lemma between the boundary map and casting along an index
equality `m = k + 1`: applying `boundaryMap k` after casting `boundaryMap m y`
through `h` agrees with the composition `boundaryMap k ∘ boundaryMap (k+1)`
applied to the appropriate cast of `y`. -/
lemma cast_boundaryMap_eq (X : Type) [TopologicalSpace X]
    (m k : ℕ) (h : m = k + 1) (y : SingularChains (m + 1) X) :
    boundaryMap k X (cast (congrArg (SingularChains · X) h) (boundaryMap m X y)) =
    boundaryMap k X (boundaryMap (k + 1) X
      (cast (congrArg (SingularChains · X) (show m + 1 = (k + 1) + 1 by omega)) y)) := by
  subst h; simp

end SingularIntComplexConstruction
end HomologyCrossProduct
