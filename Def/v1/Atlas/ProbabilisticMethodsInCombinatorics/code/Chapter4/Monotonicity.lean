/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Monotonicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option maxHeartbeats 800000

open Finset Fintype Set


noncomputable section

namespace GraphMonotonicity

/-- Product Bernoulli weight of a configuration $\omega \in \{0,1\}^n$ under parameter $p$:
    $\prod_i p^{\omega_i} (1-p)^{1 - \omega_i}$. -/
def prodWeight (n : ℕ) (p : ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, bif ω i then p else 1 - p

/-- Probability of an event $A \subseteq \{0,1\}^n$ under the product Bernoulli $\mathrm{Ber}(p)^n$
    measure: $\sum_{\omega \in A} \prod_i p^{\omega_i} (1-p)^{1 - \omega_i}$. -/
def probConst (n : ℕ) (p : ℝ) (A : Set (Fin n → Bool)) : ℝ :=
  ∑ ω : Fin n → Bool, prodWeight n p ω * A.indicator (fun _ => (1 : ℝ)) ω

end GraphMonotonicity
end
