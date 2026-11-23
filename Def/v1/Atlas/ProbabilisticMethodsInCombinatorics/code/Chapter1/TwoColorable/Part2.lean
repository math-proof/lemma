/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/TwoColorable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable

@[expose] public section

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
