/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/TwoColorable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
open Finset Fintype


namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A hypergraph on vertex set `V` is a finite collection of subsets (edges). -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

end TwoColorableHypergraph
