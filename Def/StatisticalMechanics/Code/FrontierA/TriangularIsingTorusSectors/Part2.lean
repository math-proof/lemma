/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Instance.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def triangularTorusGraph (L : Nat) [Fact (2 < L)] :
    SimpleGraph (ZMod L × ZMod L) where
  Adj := triangularTorusAdj L
  symm := by
    constructor
    rintro u v (hsquare | hdiag)
    · apply Or.inl
      exact ((onsTorusGraph L).adj_comm u v).mp hsquare
    · rcases hdiag with hdiag | hdiag
      · exact Or.inr (Or.inr <| by
          constructor
          · linear_combination -hdiag.1
          · linear_combination -hdiag.2)
      · exact Or.inr (Or.inl <| by
          constructor
          · linear_combination -hdiag.1
          · linear_combination -hdiag.2)
  loopless := by
    have hne : (1 : ZMod L) ≠ 0 := by
      letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
      exact one_ne_zero
    refine ⟨?_⟩
    intro v hv
    rcases hv with hsquare | hdiag
    · exact (onsTorusGraph L).loopless.irrefl v hsquare
    · rcases hdiag with hdiag | hdiag
      · exact hne (by linear_combination -hdiag.1)
      · exact hne (by linear_combination hdiag.1)

end StatMech.FrontierA
