/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/ListChromatic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable.Part2
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.ListChromatic
set_option maxHeartbeats 800000


namespace ListChromatic

open Finset

/-- A list assignment on a vertex set `V` is a function assigning each vertex a finite
list of available colors. -/
abbrev ListAssignment (V : Type*) (C : Type*) := V → Finset C

end ListChromatic
