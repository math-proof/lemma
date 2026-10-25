/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Theorem.Combinatorics.Order.ErdosSzekeres


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-- An increasing subsequence of `f` of length `k`: index- and value-strict. -/
def IsIncrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ i) < f (φ j))

/-- A decreasing subsequence of `f` of length `k`: index-strict, values strictly
decrease. -/
def IsDecrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ j) < f (φ i))

/-- There is an increasing subsequence of length `k` ending exactly at `p`. -/
def IsIncrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsIncrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- There is a decreasing subsequence of length `k` ending exactly at `p`. -/
def IsDecrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsDecrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

end MathlibExt.Combinatorics.Order.ErdosSzekeres
