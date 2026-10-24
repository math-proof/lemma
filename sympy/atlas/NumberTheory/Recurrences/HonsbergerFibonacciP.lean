/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Fib.Basic
import Lean.Elab.Tactic.Omega

/-! # Honsberger's identity for Fibonacci p-numbers

This file defines the Fibonacci `p`-numbers, proves their basic recurrence properties and their
specialization to the ordinary Fibonacci numbers, and proves Honsberger's identity.
-/

namespace MetaMathlibExt

/-- Fibonacci `p`-numbers with `F_p(0)=0`, `F_p(r)=1` for `1 ≤ r ≤ p`, and
`F_p(r)=F_p(r-1)+F_p(r-p-1)` for `r>p`. Definition binds source lines 79-85
with source-text SHA-256 `d9bb7efe9d48a303e5c3db6559ba63bcbaf2967585215ca8b11ee32311955a00`.
From `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex`,
source-file SHA-256 `dad9ca89271449561bda39a96e5705728a24469f6106405f6b2cc021c3d16524`,
stable ID `jis_grounded_9dbbcac802edaa76c96bd1ff`. Corrected accounting:
2 mentions / 1 paper / 1 proof use. Excludes the downstream generalized
Leonardo identity and the separate finite-sum identity. -/
def fibonacciP (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
    if r + 1 ≤ p then 1 else fibonacciP p r + fibonacciP p (r - p)
termination_by r => r
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)
end MetaMathlibExt
