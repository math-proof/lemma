/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProjectionTheory.code.MultiplicativeConvolution
import Lemma.Real.Atlas.v1.ProjectionTheory.code.MultiplicativeConvolution
import Lemma.Real.Atlas.v1.ProjectionTheory.code.LinnikLargeSieve
import Def.v1.Atlas.ProjectionTheory.code.LinnikLargeSieve
open Finset Complex Nat BigOperators


noncomputable section

namespace MultiplicativeConvolution

/-- Multiplicative convolution on `ZMod q`:
$(f *_M g)(a) = \sum_{b, c \in \mathbb{Z}/q,\ bc = a} f(b)\, g(c)$. -/
def mulConv_ZMod (q : ℕ) [NeZero q] (f g : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  ∑ b : ZMod q, ∑ c : ZMod q, if b * c = a then f b * g c else 0

/-- The projection $\pi_q f : \mathbb{Z}/q \to \mathbb{C}$ of an arithmetic function
$f : \mathbb{N} \to \mathbb{C}$ truncated to $[0, N)$: at $a \in \mathbb{Z}/q$ it sums
$f(n)$ over $n < N$ with $n \equiv a \pmod q$. -/
def modProjection_arith (N : ℕ) (q : ℕ) [NeZero q] (f : ℕ → ℂ) (a : ZMod q) : ℂ :=
  ∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = a then f n else 0

/-- The mod-$q$ projection of $f$ on $\mathbb{N}$ truncated to $1 \le n < N$ (positive
integers only): $\pi_q^+ f(a) = \sum_{0 < n < N,\ n \equiv a} f(n)$. -/
def modProjection_pos (N : ℕ) (q : ℕ) [NeZero q] (f : ℕ → ℂ) (a : ZMod q) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (· ≠ 0), if ((n : ℕ) : ZMod q) = a then f n else 0

/-- Modify $f : \mathbb{N} \to \mathbb{C}$ so that its value at $0$ is set to $0$, leaving
all other values unchanged. -/
def zeroAt0 (f : ℕ → ℂ) : ℕ → ℂ := fun n => if n = 0 then 0 else f n

end MultiplicativeConvolution
end
