/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDiscrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open ZMod Finset Complex
open scoped ZMod


noncomputable section

namespace ProjectionTheory

/-- The projection $\pi_p f : \mathbb{Z}_p \to \mathbb{C}$ of a function $f : [N] \to \mathbb{C}$
to the discrete subgroup $\mathbb{Z}_p$: for each residue $a \in \mathbb{Z}_p$, sum the values
of $f$ over all $n \in [N]$ with $n \equiv a \pmod p$. -/
def discreteProjection (p : ℕ) [NeZero p] {N : ℕ} (f : Fin N → ℂ) : ZMod p → ℂ :=
  fun a => ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a), f n

end ProjectionTheory
end
