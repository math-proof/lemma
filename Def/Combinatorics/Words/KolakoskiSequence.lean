/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Kolakoski sequences

This file formalizes the self-describing run-length definition from Olivier
Bordellès and Benoit Cloitre, *Bounds for the Kolakoski Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Bordelles/bordelles7r.tex>.
-/


namespace MetaMathlibExt

/-- The one-indexed starting position of block `n` in a candidate Kolakoski
sequence. Index zero is outside the source's domain. -/
def kolakoskiBlockStart (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => kolakoskiBlockStart K (n + 1) + K (n + 1)

/-- A one-indexed Kolakoski sequence: its values are one or two, its blocks
alternate between ones and twos, and block `n` has length `K n`. -/
def IsKolakoski (K : ℕ → ℕ) : Prop :=
  K 1 = 1 ∧
    (∀ n : ℕ, 1 ≤ n → K n = 1 ∨ K n = 2) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ,
      kolakoskiBlockStart K n ≤ i →
      i < kolakoskiBlockStart K n + K n →
      K i = if n % 2 = 1 then 1 else 2

end MetaMathlibExt
