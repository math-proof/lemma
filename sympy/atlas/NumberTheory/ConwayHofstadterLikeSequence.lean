/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean -/

import Mathlib.Data.Nat.Basic

/-!
# Conway–Hofstadter-like sequences

This file formalizes the `k`-sequences introduced by John A. Pelesko in
*Generalizing the Conway-Hofstadter $10,000 Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.tex>.
-/

namespace MetaMathlibExt

/-- The one-based residue convention used in Pelesko's recurrence: a zero residue modulo `m`
is represented by `m` itself. -/
def conwayHofstadterResidue (a m : ℕ) : ℕ :=
  if a % m = 0 then m else a % m

/-- A Conway–Hofstadter-like sequence of order `k`.

For `n ≥ 3`, the two recursive indices add to `n`. The helper
`conwayHofstadterResidue` implements the source's explicit convention that residue zero modulo
`n - 1` is written as `n - 1`, rather than as zero. -/
def IsConwayHofstadterLikeSequence (k : ℕ) (c : ℕ → ℕ) : Prop :=
  c 1 = 1 ∧ c 2 = 1 ∧ ∀ n : ℕ, 3 ≤ n →
    let i := conwayHofstadterResidue (k * c (n - 1)) (n - 1)
    c n = c i + c (n - i)

end MetaMathlibExt
