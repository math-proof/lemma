/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def triangularTorusWeightedLinearCharacterSum
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real)
    (chi : Fin 2 × Fin 2) : Real :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    triangularTorusLinearCharacter chi (triangularTorusEvenHomology L F) *
      ∏ edge ∈ F, weight edge


end StatMech.FrontierA
