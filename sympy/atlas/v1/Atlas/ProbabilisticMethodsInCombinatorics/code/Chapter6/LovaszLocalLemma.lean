/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LovaszLocalLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Set Finset ENNReal

namespace LovaszLocalLemma

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The event $A_0$ is mutually independent (under $\mu$) of all sign choices of the events $A_i$ for $i \in S$: for every assignment of each $B_i$ to either $A_i$ or $A_i^c$, $\mu(A_0 \cap \bigcap_{i \in S} B_i) = \mu(A_0)\,\mu(\bigcap_{i \in S} B_i)$. -/
def IndepOfEvents (A₀ : Set Ω) (A : ι → Set Ω) (S : Finset ι)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ B : ι → Set Ω, (∀ i ∈ S, B i = A i ∨ B i = (A i)ᶜ) →
    μ (A₀ ∩ ⋂ i ∈ S, B i) = μ A₀ * μ (⋂ i ∈ S, B i)

/-- A directed graph $G$ is a dependency digraph for the family $(A_i)_{i \in \iota}$ if, for every $i$ and every finite set $S$ of indices distinct from $i$ and not adjacent to $i$ in $G$, the event $A_i$ is mutually independent of the events $\{A_j\}_{j \in S}$. -/
def IsDependencyDigraph [Fintype ι] [DecidableEq ι] (G : Digraph ι)
    [DecidableRel G.Adj] (A : ι → Set Ω)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ i : ι, ∀ S : Finset ι, (∀ j ∈ S, ¬G.Adj i j ∧ j ≠ i) →
    IndepOfEvents (A i) A S μ

/-- The out-neighborhood of $i$ in the digraph $G$, viewed as a finite set. -/
def neighbors [Fintype ι] [DecidableEq ι] (G : Digraph ι) [DecidableRel G.Adj] (i : ι) :
    Finset ι := Finset.univ.filter (G.Adj i)

set_option maxHeartbeats 800000

variable [Fintype ι] [DecidableEq ι]
