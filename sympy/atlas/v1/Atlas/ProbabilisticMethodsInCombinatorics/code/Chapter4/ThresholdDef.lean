/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/ThresholdDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.Monotonicity
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter4.Monotonicity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 1600000

open Filter Finset BigOperators

namespace MonotoneProperty

/-- A property $\mathcal{F}$ of finite subsets is **monotone (increasing)** if it is closed
under taking supersets: whenever $S \subseteq T$ and $\mathcal{F}(S)$ holds, so does $\mathcal{F}(T)$. -/
def IsMonotone {α : Type*} (ℱ : Finset α → Prop) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ⊆ T → ℱ S → ℱ T

/-- **Definition 4.3.1 (threshold function).** A sequence $q(n)$ is a threshold for a
monotone property with probability function $\mu_n(p)$ if $\mu_n(p_n) \to 0$ whenever
$p_n / q_n \to 0$, and $\mu_n(p_n) \to 1$ whenever $p_n / q_n \to \infty$. -/
def IsThreshold (probOfProperty : ℕ → ℝ → ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop (nhds 0) →
    Tendsto (fun n => probOfProperty n (p n)) atTop (nhds 0)) ∧
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop atTop →
    Tendsto (fun n => probOfProperty n (p n)) atTop (nhds 1))

end MonotoneProperty

namespace Threshold

/-- The probability under the product Bernoulli$(p)$ distribution on $2^\Omega$ that
the random subset is exactly one of the sets in $\mathcal{F}$, summing the
weights $p^{|A|}(1-p)^{|\Omega| - |A|}$ over $A \in \mathcal{F}$. -/
noncomputable def randomSubsetProb (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (𝓕 : Finset (Finset Ω)) (p : ℝ) : ℝ :=
  ∑ A ∈ 𝓕, p ^ A.card * (1 - p) ^ (Fintype.card Ω - A.card)

/-- A function $r(n)$ is a **sharp threshold** if for every $\delta > 0$, the probability
$\mu_n(p_n) \to 0$ whenever eventually $p_n \le (1 - \delta) r_n$, and
$\mu_n(p_n) \to 1$ whenever eventually $p_n \ge (1 + \delta) r_n$. -/
def IsSharpThreshold (μ : ℕ → ℝ → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ p : ℕ → ℝ, (∀ᶠ n in atTop, p n / r n ≤ 1 - δ) →
      Tendsto (fun n => μ n (p n)) atTop (nhds 0)) ∧
    (∀ p : ℕ → ℝ, (∀ᶠ n in atTop, p n / r n ≥ 1 + δ) →
      Tendsto (fun n => μ n (p n)) atTop (nhds 1))

/-- A function $r(n)$ is a **coarse threshold** if there exist constants $0 < c < C$ and
$\varepsilon > 0$ such that whenever $p_n / r_n \in [c, C]$ eventually, the property
probability is eventually bounded into $[\varepsilon, 1 - \varepsilon]$. -/
def IsCoarseThreshold (μ : ℕ → ℝ → ℝ) (r : ℕ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ p : ℕ → ℝ, (∀ᶠ n in atTop, c ≤ p n / r n ∧ p n / r n ≤ C) →
      ∀ᶠ n in atTop, ε ≤ μ n (p n) ∧ μ n (p n) ≤ 1 - ε

end Threshold

namespace GraphMonotonicity

open Finset Fintype Set

/-- A monotone property is **nontrivial** if $\mu_n(0) = 0$ and $\mu_n(1) = 1$ for all $n$. -/
def IsNontrivial (μ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, μ n 0 = 0) ∧ (∀ n, μ n 1 = 1)

end MonotoneProperty
