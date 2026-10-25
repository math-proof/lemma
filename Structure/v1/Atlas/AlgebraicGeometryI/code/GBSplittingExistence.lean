/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Fin.VecNotation
import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence
open BigOperators


namespace GBExistence

/-- A splitting type: the data of `n` integer degrees `(d_1 ≥ … ≥ d_n)`
specifying a candidate decomposition `⊕ O(d_i)` in Grothendieck-Birkhoff. -/
structure SplittingType (n : ℕ) where
  degrees : Fin n → ℤ
  sorted : ∀ i j : Fin n, i ≤ j → degrees j ≤ degrees i

end GBExistence
