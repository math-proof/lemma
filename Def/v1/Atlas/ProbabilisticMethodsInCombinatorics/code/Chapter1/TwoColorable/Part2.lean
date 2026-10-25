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
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
open Finset Fintype


namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A hypergraph is 2-colorable (Property B) if there exists a 2-coloring of its vertices
under which no edge is monochromatic. -/
def IsTwoColorable (E : Hypergraph V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ E, ¬IsMonochromatic e c

/-- A hypergraph is $k$-uniform if every edge has size exactly $k$. -/
def IsKUniform (E : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ E, e.card = k

end TwoColorableHypergraph
