/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckBirkhoff
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.Filter.Basic
public import Mathlib.Data.Fin.VecNotation
public import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence
public section

open BigOperators


namespace GBExistence

/-- A splitting type: the data of `n` integer degrees `(d_1 ≥ … ≥ d_n)`
specifying a candidate decomposition `⊕ O(d_i)` in Grothendieck-Birkhoff. -/
structure SplittingType (n : ℕ) where
  degrees : Fin n → ℤ
  sorted : ∀ i j : Fin n, i ≤ j → degrees j ≤ degrees i

end GBExistence
