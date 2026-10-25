/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence
open BigOperators


namespace GBGeometric

/-- A vector bundle on `P^1` of positive rank, presented by its Grothendieck-Birkhoff
splitting `⊕ O(d_i)` with a decreasing tuple of integer degrees. -/
structure P1VectorBundle (k : Type*) [Field k] where
  rank : ℕ
  splittingType : Fin rank → ℤ
  sorted : ∀ i j : Fin rank, i ≤ j → splittingType j ≤ splittingType i
  hrank_pos : 0 < rank

end GBGeometric
