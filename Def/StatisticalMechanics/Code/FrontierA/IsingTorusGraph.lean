/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

def isingTorusGraph (d k : Nat) : SimpleGraph (IsingDyadicTorus d k) where
  Adj x y := ∃ i : Fin d,
    y = x + isingTorusStep i ∨ x = y + isingTorusStep i
  symm := by
    constructor
    intro x y
    rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inr h⟩
    · exact ⟨i, Or.inl h⟩
  loopless := ⟨by
    intro x
    rintro ⟨i, h | h⟩
    · apply isingTorusStep_ne_zero (k := k) i
      exact add_left_cancel (h.symm.trans (add_zero x).symm)
    · apply isingTorusStep_ne_zero (k := k) i
      exact add_left_cancel (h.symm.trans (add_zero x).symm)⟩

end StatMech.FrontierA
