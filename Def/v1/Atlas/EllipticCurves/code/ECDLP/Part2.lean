/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.ECDLP


section Example_9_1

variable [Module (ZMod N) G]

/-- A triple is valid for `cfg` when `γ = a • α + b • β`, i.e. it tracks the correct
linear combination. -/
def PollardRhoTriple.IsValid (cfg : PollardRhoConfig G N) (t : PollardRhoTriple N G) : Prop :=
  t.a • cfg.α + t.b • cfg.β = t.γ

/-- A partition is valid when each class offset `δ i` equals `c i • α + d i • β`,
so applying a partition step preserves the invariant `γ = a • α + b • β`. -/
def PollardRhoConfig.PartitionValid (cfg : PollardRhoConfig G N) : Prop :=
  ∀ i : Fin cfg.r, cfg.δ i = cfg.c i • cfg.α + cfg.d i • cfg.β

/-- One step of the Pollard-ρ iteration: identify the class `i = h(γ)` and add
`(c i, d i, δ i)` to the triple. -/
def pollardRhoStep (cfg : PollardRhoConfig G N) (t : PollardRhoTriple N G) :
    PollardRhoTriple N G :=
  let i := cfg.h t.γ
  { a := t.a + cfg.c i
    b := t.b + cfg.d i
    γ := t.γ + cfg.δ i }

/-- Iterate `pollardRhoStep` starting from `t₀` for `n` steps. -/
def pollardRhoIter (cfg : PollardRhoConfig G N) (t₀ : PollardRhoTriple N G) :
    ℕ → PollardRhoTriple N G
  | 0 => t₀
  | n + 1 => pollardRhoStep cfg (pollardRhoIter cfg t₀ n)

/-- Evaluate the affine function `t ↦ a t + b` over `ZMod p` at `t`, where `ab = (a, b)`. -/
def evalAffine (ab : ZMod p × ZMod p) (t : ZMod p) : ZMod p :=
  ab.1 * t + ab.2

/-- Shoup's collision set: the set of `t ∈ ZMod p` such that two distinct affine
encodings `F i ≠ F j` (with `i < j`) collide at `t`. The generic-group adversary
can only succeed on these `t`. -/
noncomputable def collisionSet (s : ℕ) (F : Fin s → ZMod p × ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun t : ZMod p =>
    ∃ i j : Fin s, i < j ∧ F i ≠ F j ∧ evalAffine (F i) t = evalAffine (F j) t)

/-- The largest prime factor of `N > 1`, used by Shoup's bound to express the
generic-group lower bound in terms of the hardest prime-order subgroup. -/
noncomputable def largestPrimeFactor (N : ℕ) (hN : 1 < N) : ℕ :=
  (N.primeFactors).max' (Nat.nonempty_primeFactors.mpr hN)

end Example_9_1
