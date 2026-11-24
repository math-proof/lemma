module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
public import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part2
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising


abbrev kwStarDart (ι : Type*) := ι × Bool


end StatMech.FrontierA
