/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence
import Instance.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric
open BigOperators


namespace GBGeometric

set_option maxHeartbeats 400000 in

/-- Build a `P1VectorBundle` from an abstract splitting type once a positive-rank witness is given. -/
def splittingTypeToBundle (k : Type*) [Field k] {n : ℕ} (hn : 0 < n)
    (s : GBExistence.SplittingType n) : P1VectorBundle k where
  rank := n
  splittingType := s.degrees
  sorted := s.sorted
  hrank_pos := hn

end GBGeometric
