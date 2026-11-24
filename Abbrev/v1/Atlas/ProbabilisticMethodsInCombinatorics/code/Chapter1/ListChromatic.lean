module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable.Part2
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.ListChromatic
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/ListChromatic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ListChromatic

open Finset

/-- A list assignment on a vertex set `V` is a function assigning each vertex a finite
list of available colors. -/
abbrev ListAssignment (V : Type*) (C : Type*) := V → Finset C

end ListChromatic
