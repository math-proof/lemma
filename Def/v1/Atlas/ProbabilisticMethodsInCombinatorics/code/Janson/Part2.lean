/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace Janson

/-- Joint probability $\mathbb{P}(A_i \cap A_j) = \prod_{l \in S_i \cup S_j} p_l$. -/
def JansonSetup.probJoint (J : JansonSetup) (i j : Fin J.k) : ℝ :=
  ∏ l ∈ J.S i ∪ J.S j, J.prob l

/-- The dependency parameter $\Delta = \sum_{i \sim j} \mathbb{P}(A_i \cap A_j)$, summed over
ordered dependent pairs $(i,j)$. -/
def JansonSetup.delta (J : JansonSetup) : ℝ :=
  ∑ i : Fin J.k, ∑ j : Fin J.k,
    if J.dep i j then J.probJoint i j else 0

/-- Probability that none of the bad events occur, i.e. $\mathbb{P}(\bigcap_i \overline{A_i})$,
expressed as a sum over the random subset $T$ of coordinates that are present. -/
def JansonSetup.probNone (J : JansonSetup) : ℝ :=
  ∑ T : Finset (Fin J.N),
    (if ∀ i : Fin J.k, ¬(J.S i ⊆ T) then
      (∏ j ∈ T, J.prob j) * (∏ j ∈ Finset.univ.filter (fun j => j ∉ T), (1 - J.prob j))
    else 0)

/-- Probability that the random subset of present coordinates equals exactly $T$. -/
def JansonSetup.probSubset (J : JansonSetup) (T : Finset (Fin J.N)) : ℝ :=
  (∏ i ∈ T, J.prob i) * (∏ i ∈ Finset.univ \ T, (1 - J.prob i))

/-- Given a subset $T$ of present coordinates, counts the number of bad events $A_i$ that
occur, i.e. the number of indices $i$ with $S_i \subseteq T$. -/
def JansonSetup.countEvents (J : JansonSetup) (T : Finset (Fin J.N)) : ℕ :=
  (Finset.univ.filter (fun i => J.S i ⊆ T)).card

/-- Lower-tail probability $\mathbb{P}(X \le \mu - t)$ where $X = \sum_i \mathbf{1}_{A_i}$
counts how many bad events occur. -/
def JansonSetup.probLowerTail (J : JansonSetup) (t : ℝ) : ℝ :=
  ∑ T ∈ Finset.powerset Finset.univ,
    if (J.countEvents T : ℝ) ≤ J.mu - t then J.probSubset T else 0

/-- Chain-rule lemma underpinning Janson's inequality: there exist factors $r_i \le 1$
such that $\mathbb{P}(\text{no bad event}) = \prod_i (1 - r_i)$ and
$\sum_i r_i \ge \mu - \Delta/2$. This is the Harris-style decomposition used in the proof
of Theorem 8.1.2. -/
def mu_triangles (n : ℕ) (p : ℝ) : ℝ :=
  (n.choose 3 : ℝ) * p ^ 3

/-- Janson dependency parameter for triangles in $G(n,p)$: counts ordered pairs of
triangles sharing an edge, weighted by the joint probability $p^5$. -/
def delta_triangles (n : ℕ) (p : ℝ) : ℝ :=
  (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p ^ 5

/-- Probability that $G(n,p)$ is triangle-free, computed under the binomial random graph
measure on $\mathrm{Fin}\, n$. -/
def triangleFreeProb (n : ℕ) (p : ↑unitInterval) : ℝ :=
  (SimpleGraph.binomialRandom (Fin n) p).real {G | G.CliqueFree 3}

/-- Triangle-free probability at edge density $p = c/n$, returning $0$ if $c/n$ falls
outside the unit interval. -/
def triangleFreeProb_cn (c : ℝ) (n : ℕ) : ℝ :=
  if h : c / (n : ℝ) ∈ unitInterval then
    triangleFreeProb n ⟨c / (n : ℝ), h⟩
  else 0

end Janson
end
