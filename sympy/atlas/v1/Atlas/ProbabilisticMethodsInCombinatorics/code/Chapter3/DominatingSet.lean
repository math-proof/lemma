/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/DominatingSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace DominatingSet

open SimpleGraph Finset Real BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set $D \subseteq V$ is a dominating set of $G$ if every vertex outside $D$ has a
neighbor in $D$. -/
def IsDominatingSet (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v : V, v ∉ D → ∃ u ∈ D, G.Adj v u

/-- The Bernoulli probability weight of a subset $S \subseteq V$ under independent inclusion
with parameter $p$: equals $p^{|S|} (1-p)^{n-|S|}$ where $n = |V|$. -/
noncomputable def bernoulliWeight (p : ℝ) (S : Finset V) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card V - S.card)
