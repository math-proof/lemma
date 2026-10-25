/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def triangularTorusEvenHomology (L : Nat)
    (F : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 × Fin 2 :=
  by
    classical
    exact
      (⟨(F.filter (triangularTorusXSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩,
       ⟨(F.filter (triangularTorusYSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩)


noncomputable def triangularTorusWeightedSpinCharacterSum
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) : Complex :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    (ons_spinCharacter a b (triangularTorusEvenHomology L F) : Complex) *
      ∏ edge ∈ F, weight edge

end StatMech.FrontierA
