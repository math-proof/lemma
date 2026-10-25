/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


def kwStarDartEdge {ι : Type*} (d : kwStarDart ι) : Sym2 (Unit ⊕ ι) :=
  s(kwStarDartTail d, kwStarDartHead d)


noncomputable def kwStarTransition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    Matrix (kwStarDart ι) (kwStarDart ι) ℂ :=
  fun d2 d1 =>
    if d1.2 = false ∧ d2.2 = true ∧ d1.1 ≠ d2.1 then
      x (kwStarDartEdge d1) * phase d1 d2
    else 0


end StatMech.FrontierA
