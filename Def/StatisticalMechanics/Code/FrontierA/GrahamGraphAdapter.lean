/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamGraph (E : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := s(x, y) ∈ E ∧ x ≠ y
  symm := by
    constructor
    intro x y h
    exact ⟨by simpa [Sym2.eq_swap] using h.1, h.2.symm⟩
  loopless := ⟨by
    intro x h
    exact h.2 rfl⟩

end StatMech.FrontierA
