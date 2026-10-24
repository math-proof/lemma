/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section Example_9_1

/-- Probability that the first `n` steps of a random walk on a set of size `N`
all land on distinct vertices (the birthday-product `∏_{i<n} (1 - (i+1)/N)`). -/
noncomputable def birthdayProb (N : ℕ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - (↑(i + 1) : ℝ) / ↑N)

/-- Expected value of the rho-length for a random walk on a set of size `N`,
expressed as `∑_{n<N} birthdayProb N n`. Theorem 9.3 shows this is asymptotic to `√(πN/2)`. -/
noncomputable def expectedRho (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, birthdayProb N n

/-- A triple `(a, b, γ)` tracked by the Pollard-ρ walk for the DLP: scalars
`a, b ∈ ℤ/Nℤ` together with the corresponding group element `γ = a·α + b·β`. -/
@[ext]
structure PollardRhoTriple (N : ℕ) (G : Type*) where
  a : ZMod N
  b : ZMod N
  γ : G

/-- Configuration for Pollard's rho algorithm (Algorithm 9.5): the generator `α`,
the target `β = log_α^{-1} β`, the number `r` of partition classes (with `0 < r`),
the per-class scalar offsets `c`, `d` and group offsets `δ`, and a partition map `h : G → Fin r`. -/
structure PollardRhoConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N] where
  α : G
  β : G
  r : ℕ
  hr : 0 < r
  c : Fin r → ZMod N
  d : Fin r → ZMod N
  δ : Fin r → G
  h : G → Fin r

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

/-- The largest prime factor divides `N`. -/
lemma largestPrimeFactor_dvd (N : ℕ) (hN : 1 < N) :
    largestPrimeFactor N hN ∣ N := by
  have h := Finset.max'_mem _ (Nat.nonempty_primeFactors.mpr hN)
  exact (Nat.mem_primeFactors.mp h).2.1

/-- Canonical ring hom `ZMod N → ZMod (largestPrimeFactor N)` induced by the divisibility
`lp(N) ∣ N`, used to reduce a generic DLP on `ZMod N` to the prime-order subgroup. -/
noncomputable def projToLargestPrime (N : ℕ) (hN : 1 < N) :
    ZMod N →+* ZMod (largestPrimeFactor N hN) :=
  ZMod.castHom (largestPrimeFactor_dvd N hN) (ZMod (largestPrimeFactor N hN))

/-- Expected-value lower bound used in Corollary 9.10: `∑_{m<M} (1 - m²/(2p))`, which
bounds the expected number of group operations for a Las Vegas DLP algorithm. -/
noncomputable def lasVegasExpectedLB (p M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (1 - (↑m : ℝ) ^ 2 / (2 * ↑p))

/-- Shoup's combinatorial constraint on a Las Vegas DLP work function `w`: for every
`s`, at most `s(s-1)/2` instances `t` are solved by `w t ≤ s` queries. -/
def LasVegasShoupConstraint (w : ZMod p → ℕ) : Prop :=
  ∀ s : ℕ, (Finset.univ.filter (fun t : ZMod p => w t ≤ s)).card ≤ s * (s - 1) / 2

/-- Configuration for Pollard-ρ with distinguished points (Algorithm 9.6): extends
`PollardRhoConfig` with a boolean predicate `B : G → Bool` identifying distinguished
group elements that get logged for collision detection. -/
structure PollardRhoDPConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N]
    extends PollardRhoConfig G N where
  B : G → Bool

variable [Module (ZMod N) G]

/-- A triple is distinguished when its `γ`-component is flagged by `B`. -/
def PollardRhoTriple.IsDistinguished
    (dpCfg : PollardRhoDPConfig G N) (t : PollardRhoTriple N G) : Prop :=
  dpCfg.B t.γ = true

/-- Two distinguished-point triples are a "DP collision" when both are distinguished
and have the same `γ` (only then does the algorithm record a useful collision). -/
def PollardRhoDPConfig.IsCollision
    (dpCfg : PollardRhoDPConfig G N)
    (t₁ t₂ : PollardRhoTriple N G) : Prop :=
  t₁.IsDistinguished dpCfg ∧ t₂.IsDistinguished dpCfg ∧ t₁.γ = t₂.γ
