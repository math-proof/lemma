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

set_option maxHeartbeats 800000

open Filter Real
open scoped Topology

noncomputable section

namespace Janson

/-- A Janson setup consists of $N$ independent Bernoulli variables with success probabilities
`prob i ∈ [0,1]` and a family of $k$ "bad events" indexed by subsets $S_i \subseteq \{0,\dots,N-1\}$,
where event $i$ occurs iff every coordinate in $S_i$ is present in the random subset. -/
structure JansonSetup where
  N : ℕ
  k : ℕ
  prob : Fin N → ℝ
  S : Fin k → Finset (Fin N)
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_le_one : ∀ i, prob i ≤ 1

/-- Probability that the $i$-th bad event $A_i$ occurs, i.e.
$\mathbb{P}(A_i) = \prod_{j \in S_i} p_j$. -/
def JansonSetup.probEvent (J : JansonSetup) (i : Fin J.k) : ℝ :=
  ∏ j ∈ J.S i, J.prob j

/-- The expected number of bad events, $\mu = \sum_{i=1}^{k} \mathbb{P}(A_i)$. -/
def JansonSetup.mu (J : JansonSetup) : ℝ :=
  ∑ i : Fin J.k, J.probEvent i

/-- Dependency relation between bad events: events $A_i$ and $A_j$ are dependent iff
$i \ne j$ and $S_i \cap S_j \ne \emptyset$. -/
def JansonSetup.dep (J : JansonSetup) (i j : Fin J.k) : Prop :=
  i ≠ j ∧ (J.S i ∩ J.S j).Nonempty

/-- Decidability of the dependency relation. -/
instance (J : JansonSetup) (i j : Fin J.k) : Decidable (J.dep i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

/-- Janson upper bound applied to triangles in $G(n, c/n)$:
$\mathbb{P}(G \text{ triangle-free}) \le \exp(-\mu + \Delta/2)$. -/
end Janson

namespace JansonInequalities

open Filter Asymptotics Real

/-- Bundle of asymptotic data for triangles in $G(n, p(n))$: triangle-free probability,
Janson parameters $\mu$ and $\Delta$ with their correct asymptotic order. -/
structure TriangleFreeGnpData (p : ℕ → ℝ) where
  prob_tf : ℕ → ℝ
  μ : ℕ → ℝ
  Δ : ℕ → ℝ
  prob_tf_pos : ∀ᶠ n in atTop, 0 < prob_tf n
  prob_tf_le_one : ∀ᶠ n in atTop, prob_tf n ≤ 1
  μ_isTheta : μ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
  Δ_isTheta : Δ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
  Δ_pos : ∀ᶠ n in atTop, 0 < Δ n

/-- For any fixed $k \in \mathbb{N}$, $(n - k) \asymp n$ as $n \to \infty$. -/
lemma isTheta_natCast_sub_const (k : ℕ) :
    (fun n : ℕ => (n : ℝ) - (k : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · apply IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    simp only [one_mul]
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)]
    linarith
  · apply IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop (2 * k)] with n hn
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n from by omega)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)]
    have : (n : ℝ) / 2 ≤ (n : ℝ) - k := by
      have hcast : (2 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith

/-- Constructs a `TriangleFreeGnpData` bundle for a probability sequence $p(n)$ that is
eventually positive and bounded away from $1$. The triangle-free probability used is the
naive empty-graph bound $(1-p)^{\binom{n}{2}}$ for the lower bound. -/
def triangleFreeGnpData_exists (p : ℕ → ℝ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_le : ∀ᶠ n in atTop, p n ≤ 0.99) :
    TriangleFreeGnpData p := by
  refine ⟨fun n => (1 - p n) ^ Nat.choose n 2,
         fun n => Janson.mu_triangles n (p n),
         fun n => Janson.delta_triangles n (p n), ?_, ?_, ?_, ?_, ?_⟩
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_pos; linarith
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_le_one₀ (by linarith) (by linarith)
  ·
    show (fun n : ℕ => (n.choose 3 : ℝ) * p n ^ 3) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
    exact (isTheta_choose 3).mul (isTheta_refl _ _)
  ·
    show (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p n ^ 5) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
    have h_coeff : (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4) := by
      have h1 := isTheta_choose 2
      have h2 := isTheta_natCast_sub_const 2
      have h3 := isTheta_natCast_sub_const 3
      have hmul := h1.mul h2 |>.mul h3
      have heq : (fun n : ℕ => (n : ℝ) ^ 2 * (↑n) * (↑n)) = (fun n : ℕ => (n : ℝ) ^ 4) := by
        ext n; ring
      rwa [heq] at hmul
    exact h_coeff.mul (isTheta_refl _ _)
  ·
    filter_upwards [hp_pos, Filter.eventually_ge_atTop 4] with n hp hn
    simp only [Janson.delta_triangles]
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hcn2 : (0 : ℝ) < (n.choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
    apply mul_pos
    · apply mul_pos
      · exact mul_pos hcn2 hn2
      · exact hn3
    · positivity

/-- Janson II applied to triangles in $G(n, p(n))$ via the bundle from
`triangleFreeGnpData_exists`: $\mathbb{P}(G \text{ triangle-free}) \le
\exp(-\mu^2 / (2\Delta))$. -/
end JansonInequalities

namespace Janson

open Real

/-- Parametric form of Janson's inequality (Theorem 8.1.10): for every $q \in [0,1]$,
$$ \mathbb{P}(X = 0) \le \exp(-q\mu + q^2 \Delta / 2). $$ -/
end Janson
