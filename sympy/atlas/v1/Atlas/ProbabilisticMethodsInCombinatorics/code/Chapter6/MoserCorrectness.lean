/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Finset

namespace MoserCorrectness

/-- A propositional literal over $n$ variables: a variable index in $\text{Fin}\ n$ together with a Boolean polarity (`true` = positive, `false` = negated). -/
structure Literal (n : ℕ) where
  var : Fin n
  polarity : Bool

/-- A $k$-clause over $n$ variables: an indexed family of $k$ literals (interpreted as their disjunction). -/
structure Clause (n k : ℕ) where
  lits : Fin k → Literal n

/-- A Boolean assignment to $n$ variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- The clause $C$ is satisfied by the assignment $\sigma$ if at least one of its literals evaluates to `true`. -/
def Clause.satisfied (C : Clause n k) (σ : Assignment n) : Prop :=
  ∃ i : Fin k, (C.lits i).polarity = σ (C.lits i).var

/-- A $k$-CNF formula over $n$ variables consisting of $m$ clauses, each of width exactly $k$. -/
structure KCNF (n m k : ℕ) where
  clauses : Fin m → Clause n k

/-- A $k$-CNF formula is satisfiable if some assignment satisfies every one of its clauses. -/
def KCNF.satisfiable (φ : KCNF n m k) : Prop :=
  ∃ σ : Assignment n, ∀ i : Fin m, (φ.clauses i).satisfied σ

/-- Two clauses share a variable if some literal of $C$ and some literal of $D$ refer to the same variable index. -/
def Clause.sharesVarWith (C D : Clause n k) : Prop :=
  ∃ i j : Fin k, (C.lits i).var = (D.lits j).var

/-- A $k$-CNF formula has bounded degree $d$ if every clause shares a variable with at most $d$ other clauses. -/
def KCNF.boundedDegree (φ : KCNF n m k) (d : ℕ) : Prop :=
  ∀ i : Fin m, ∀ (S : Finset (Fin m)),
    (∀ j ∈ S, j ≠ i ∧ (φ.clauses i).sharesVarWith (φ.clauses j)) →
    S.card ≤ d

/-- Resample function used by Moser's algorithm: given a list `vars` of variable indices and fresh random bits `b`, replace the values of $\sigma$ on the listed variables by the corresponding bits and leave the others unchanged. -/
noncomputable def resampleFn {n k : ℕ} (vars : Fin k → Fin n)
    (σ : Fin n → Bool) (b : Fin k → Bool) : Fin n → Bool :=
  fun v => if h : ∃ i, vars i = v then b h.choose else σ v

/-- The state of the resampling process after $t$ steps, starting from $\sigma_0$, where step $t$ resamples the variables `vars_seq t` using the random bits `bits t`. -/
noncomputable def stepSt {n k : ℕ} (vars_seq : ℕ → Fin k → Fin n) (σ₀ : Fin n → Bool)
    (bits : ℕ → Fin k → Bool) : ℕ → Fin n → Bool
  | 0 => σ₀
  | t + 1 => resampleFn (vars_seq t) (stepSt vars_seq σ₀ bits t) (bits t)

/-- Bundle produced by the entropy-compression argument: a set of "failing" random strings of size at most $2^n \cdot 2^{\ell(k-1)+1}$, together with a proof that any string outside this set witnesses satisfiability of $\varphi$. -/
structure EntropyCompression (n m k ℓ : ℕ) (φ : KCNF n m k) where
  failingStrings : Finset (Fin (2 ^ (k * ℓ)))
  card_bound : failingStrings.card ≤ 2 ^ n * 2 ^ (ℓ * (k - 1) + 1)
  success_implies_sat : ∀ x : Fin (2 ^ (k * ℓ)), x ∉ failingStrings → φ.satisfiable

/-- Existence of the entropy-compression bundle (Lemmas 6.6.7–6.6.8): for any $k$-CNF formula with $k \ge 3$ and bounded degree $2^{k-3}$, and any $\ell \ge 1$, the set of $\ell$-step random-bit strings for which Moser's algorithm fails has cardinality at most $2^n \cdot 2^{\ell(k-1)+1}$, and every successful string yields a satisfying assignment. -/
end MoserCorrectness
