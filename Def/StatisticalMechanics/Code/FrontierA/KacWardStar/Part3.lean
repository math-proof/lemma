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
import Abbrev.StatisticalMechanics.Code.FrontierA.KacWardStar
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


def kwStarDartTail {ι : Type*} : kwStarDart ι -> Unit ⊕ ι
  | (leaf, false) => Sum.inr leaf
  | (_, true) => Sum.inl Unit.unit


def kwStarDartHead {ι : Type*} : kwStarDart ι -> Unit ⊕ ι
  | (_, false) => Sum.inl Unit.unit
  | (leaf, true) => Sum.inr leaf


end StatMech.FrontierA
