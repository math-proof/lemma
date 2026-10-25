/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def kwIsoradialDualityNormalization
    (Vertex : Type*) [Fintype Vertex] (theta : E -> Real) : Complex :=
  (2 : Complex) ^ Fintype.card Vertex *
    ∏ edge : E, (1 + (Real.cos (theta edge) : Complex))

end StatMech.FrontierA
