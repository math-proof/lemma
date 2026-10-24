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
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable

set_option maxHeartbeats 800000

namespace ListChromatic

open Finset

/-- `IsKChoosable n k` says that the complete bipartite graph $K_{n,n}$ is $k$-choosable
in the combinatorial sense: for any color set $C$ and any pair of list assignments
$L, R : [n] \to \binom{C}{\ge k}$, there exist representatives $cL_i \in L_i$ and
$cR_j \in R_j$ with $cL_i \ne cR_j$ for all $i, j$. -/
def IsKChoosable (n k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (L R : Fin n → Finset C),
    (∀ i, k ≤ (L i).card) →
    (∀ j, k ≤ (R j).card) →
    ∃ (cL : Fin n → C) (cR : Fin n → C),
      (∀ i, cL i ∈ L i) ∧
      (∀ j, cR j ∈ R j) ∧
      (∀ i j, cL i ≠ cR j)

/-- A list assignment on a vertex set `V` is a function assigning each vertex a finite
list of available colors. -/
abbrev ListAssignment (V : Type*) (C : Type*) := V → Finset C

/-- `G.IsListColorable' L` says that there is a proper coloring of `G` choosing each
vertex's color from its list `L v`. -/
def IsListColorable' {C : Type*} (L : ListAssignment V C) : Prop :=
  ∃ f : V → C, (∀ v, f v ∈ L v) ∧ (∀ v w, G.Adj v w → f v ≠ f w)

/-- A graph is $k$-choosable if every list assignment with lists of size at least $k$
admits a proper list coloring. -/
def IsKChoosable' (k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] (L : ListAssignment V C),
    (∀ v, k ≤ (L v).card) → G.IsListColorable' L

/-- The list chromatic number $ch(G)$ of a graph $G$: the smallest $k$ for which $G$
is $k$-choosable, as an element of $\mathbb{N} \cup \{\infty\}$. -/
noncomputable def listChromaticNumber : ℕ∞ :=
  ⨅ k ∈ {n : ℕ | G.IsKChoosable' n}, (k : ℕ∞)

/-- The average degree of a finite graph $G$, i.e. $\frac{1}{|V|} \sum_{v} \deg(v)$
(or $0$ when $V$ is empty). -/
noncomputable def averageDegree [Fintype V] [DecidableRel G.Adj] : ℝ :=
  if Fintype.card V = 0 then 0
  else (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ)

end SimpleGraph

/-- (Theorem 1.4.5, Saxton–Thomason 2015) For every $\varepsilon > 0$ there is a $D > 0$
such that every graph $G$ with average degree at least $D$ satisfies
$ch(G) \ge (1 - \varepsilon) \log_2 \bar d(G)$. -/
instance instDecidableRelAdjCompleteBipartiteGraph {V W : Type*} [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro v w; simp only [completeBipartiteGraph_adj]; infer_instance
