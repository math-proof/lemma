/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount


namespace BertiniArithmetic

/-- An abstract bundle of data for a smooth subvariety of `ℙⁿ` of dimension `d` together with
its space of hyperplanes — used to state Bertini's theorem combinatorially. -/
structure SmoothSubvariety where
  n : ℕ
  d : ℕ
  HyperplaneIndex : Type
  hdn : d < n

end BertiniArithmetic
