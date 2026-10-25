/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LargeSieveSize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.LinnikLargeSieve
import Lemma.Real.Atlas.v1.ProjectionTheory.code.LinnikLargeSieve
open Finset Complex Real


noncomputable section

namespace LargeSieveSize

/-- The image $\pi_p(A) \subseteq \mathbb{Z}_p$ of `A ⊆ ℕ` under reduction modulo `p`. -/
def projImage (A : Finset ℕ) (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.image (fun n : ℕ => (n : ZMod p)) A

/-- Predicate: `A` has small projections, meaning `|π_p(A)| ≤ 0.99 p` for every prime
`p ∈ P_{N^{1/2}}`. This is the hypothesis of Corollary 5. -/
def hasSmallProjections (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ p ∈ LinnikLargeSieve.primesInRange (Nat.sqrt N),
    ∀ hp : Nat.Prime p,
      haveI : NeZero p := ⟨hp.ne_zero⟩
      (projImage A p).card ≤ Nat.floor (0.99 * (p : ℝ))

/-- Indicator function `1_A : Fin N → ℂ`, where index `n : Fin N` corresponds to the integer
`n + 1 ∈ [1, N]`. -/
def indicatorFn (A : Finset ℕ) (N : ℕ) : Fin N → ℂ :=
  fun n => if (n : ℕ) + 1 ∈ A then 1 else 0

end LargeSieveSize
end
