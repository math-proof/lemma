/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.Basic

@[expose] public section

set_option maxHeartbeats 400000


namespace LovaszLocalLemma

open Set Finset

/-- The coloring $c : \mathbb{R} \to \text{Fin}\ k$ is multicolored on the set $T$ if every color $i \in \text{Fin}\ k$ is attained by some $x \in T$. -/
def IsMulticolored (k : ℕ) (c : ℝ → Fin k) (T : Set ℝ) : Prop :=
  ∀ i : Fin k, ∃ x ∈ T, c x = i

/-- The translate of $S \subseteq \mathbb{R}$ by $t$, i.e. $S + t = \{s + t : s \in S\}$. -/
def translate (S : Set ℝ) (t : ℝ) : Set ℝ := (· + t) '' S

/-- The set of $k$-colorings of $\mathbb{R}$ that are multicolored on the translate $S + t$. -/
def goodColorings (k : ℕ) (S : Finset ℝ) (t : ℝ) : Set (ℝ → Fin k) :=
  {c | IsMulticolored k c (translate (↑S) t)}

/-- The arithmetic progression $a, a+d, \dots, a+(k-1)d$ is monochromatic under the $\{0,1\}$-coloring $c$ of $\mathbb{Z}$ if all of its $k$ terms have the same color as $a$. -/
def IsMonochromaticAP (c : ℤ → Bool) (k : ℕ) (a d : ℤ) : Prop :=
  ∀ i : Fin k, c (a + ↑(i : ℕ) * d) = c a

end LovaszLocalLemma
