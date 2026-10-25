/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HyperfactorialPartition.lean -/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Def.NumberTheory.HyperfactorialPartition
/-! Provenance: concept `jis_sem_c632991dc77d0efec89f490f`,
source statement `jis_2803b664db749f0c99721a41`. -/


namespace MetaMathlibExt

/-- Hyperfactorial partition of `n` (concept `jis_sem_c632991dc77d0efec89f490f`,
source statement `jis_2803b664db749f0c99721a41`): a finite one-based digit list
`[h₁, …, hₖ]!` (clause `digits`) with `hᵢ ≤ 2 * i` for `1 ≤ i ≤ k`
(clause `bounds`, with `0 ≤ hᵢ` automatic for `ℕ`) and
`n = ∑_{i=1}^k hᵢ * i!` (clause `value`). Zero-based `Fin k` index `i`
translates to one-based source index `i.val + 1`. -/
structure HyperfactorialPartition (n : ℕ) where
  /-- Length `k` of the digit list (clause `digits`;
  source statement `jis_2803b664db749f0c99721a41`). -/
  k : ℕ
  /-- One-based digit list `[h₁, …, hₖ]!` as a `Fin k` vector of naturals
  (clause `digits`; source statement `jis_2803b664db749f0c99721a41`). -/
  digits : Fin k → ℕ
  /-- Upper digit bound `hᵢ ≤ 2 * i` at one-based index `i.val + 1`
  (clause `bounds`; source statement `jis_2803b664db749f0c99721a41`). -/
  bound : ∀ i : Fin k, digits i ≤ 2 * (i.val + 1)
  /-- The final digit is nonzero when `k > 0`, ruling out trailing-zero extensions. -/
  normalized : HyperfactorialDigitsNormalized k digits
  /-- Exact value `n = ∑_{i=1}^k hᵢ * i!` (clause `value`;
  source statement `jis_2803b664db749f0c99721a41`). -/
  value : n = Finset.sum Finset.univ (fun i : Fin k => digits i * Nat.factorial (i.val + 1))

end MetaMathlibExt
