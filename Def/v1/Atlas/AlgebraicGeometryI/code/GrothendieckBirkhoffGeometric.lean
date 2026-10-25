/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence
import Structure.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric
open BigOperators


namespace GBGeometric

/-- Total degree of `E = ⊕ O(d_i)` on `P^1`: `deg E = ∑ d_i`. -/
def P1VectorBundle.degree {k : Type*} [Field k] (E : P1VectorBundle k) : ℤ :=
  ∑ i, E.splittingType i

/-- Forget the positivity of the rank and recover the abstract `SplittingType` record. -/
def P1VectorBundle.toSplittingType {k : Type*} [Field k]
    (E : P1VectorBundle k) : GBExistence.SplittingType E.rank where
  degrees := E.splittingType
  sorted := E.sorted

end GBGeometric
