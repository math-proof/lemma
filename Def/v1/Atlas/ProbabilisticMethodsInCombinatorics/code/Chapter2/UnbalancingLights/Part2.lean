/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.UnbalancingLights
open Finset BigOperators


namespace UnbalancingLights

/-- The sign-flip operation packaged as an `Equiv` on Boolean vectors, used to
relabel sums over $\{-1, +1\}^n$. -/
def signFlipEquiv {n : ℕ} (a : Fin n → ℤ) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  (signFlip_involutive a).toPerm (signFlip a)

/-- A "cross edge" in the $k$-partite hypergraph on $\mathrm{Fin}\,k \times \mathrm{Fin}\,n$:
a $k$-element set $e$ that picks exactly one vertex from each "part"
$\{i\} \times \mathrm{Fin}\,n$. -/
def IsCrossEdge {k n : ℕ} (e : Finset (Fin k × Fin n)) : Prop :=
  e.card = k ∧ ∀ i : Fin k, (e.filter (fun p => p.1 = i)).card = 1

/-- Discrepancy of a coloring on $k$-subsets of $S$: the signed sum
$\sum_{e \in \binom{S}{k}} \mathrm{color}(e)$ viewed as a real number. -/
noncomputable def discrepancy {k n : ℕ} (color : Finset (Fin k × Fin n) → ℤ)
    (S : Finset (Fin k × Fin n)) : ℝ :=
  ∑ e ∈ Finset.powersetCard k S, (color e : ℝ)

end UnbalancingLights
