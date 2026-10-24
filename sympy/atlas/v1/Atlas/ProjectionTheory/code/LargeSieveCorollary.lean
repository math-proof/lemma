/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LargeSieveCorollary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProjectionTheory.code.LargeSieveAvg

open Finset Real

namespace LargeSieve

/-- The set of primes in the dyadic interval `[M/2, M]`. -/
noncomputable def primesDyadic (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- The cardinality of the fiber of `A` over `a ∈ ZMod p`, i.e. the number of `n ∈ A` with
`n ≡ a (mod p)`. -/
def fiberCard (A : Finset ℕ) (p : ℕ) (a : ZMod p) : ℕ :=
  (A.filter (fun (n : ℕ) => (n : ZMod p) = a)).card

/-- Average deviation from equidistribution modulo `p`:
$\frac{1}{p} \sum_{a \in \mathbb{Z}_p} \big|\, |A \cap (a + p\mathbb{Z})| - |A|/p \,\big|$. -/
noncomputable def avgDeviationMod (A : Finset ℕ) (p : ℕ) : ℝ :=
  if hp : p = 0 then 0
  else
    haveI : NeZero p := ⟨hp⟩
    (1 / (p : ℝ)) * ∑ a : ZMod p, |((fiberCard A p a : ℝ) - (A.card : ℝ) / (p : ℝ))|

/-- The indicator function `1_A : Fin N → ℂ`, where index `n` corresponds to the integer
`n.val + 1 ∈ [1, N]`. -/
noncomputable def indicatorFin (N : ℕ) (A : Finset ℕ) : Fin N → ℂ :=
  fun n => if (n.val + 1) ∈ A then 1 else 0

/-- $L^2$ version of the average large sieve bound: for `A ⊆ [1, N]`, the average over primes
`p ∈ P_{N^{1/2}}` of `(avgDeviationMod A p)^2` is at most `C₁ · (log N)^2 · N^{1/2}`. -/
end LargeSieve
