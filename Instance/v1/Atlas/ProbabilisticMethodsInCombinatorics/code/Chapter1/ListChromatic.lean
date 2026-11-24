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
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.ListChromatic.Part2
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/ListChromatic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- (Theorem 1.4.5, Saxton–Thomason 2015) For every $\varepsilon > 0$ there is a $D > 0$
such that every graph $G$ with average degree at least $D$ satisfies
$ch(G) \ge (1 - \varepsilon) \log_2 \bar d(G)$. -/
instance instDecidableRelAdjCompleteBipartiteGraph {V W : Type*} [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro v w; simp only [completeBipartiteGraph_adj]; infer_instance

