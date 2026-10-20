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

namespace IsKolakoski

theorem one {K : ℕ → ℕ} (h : IsKolakoski K) : K 1 = 1 :=
  h.1

theorem value_eq_one_or_two {K : ℕ → ℕ} (h : IsKolakoski K)
    {n : ℕ} (hn : 1 ≤ n) : K n = 1 ∨ K n = 2 :=
  h.2.1 n hn

theorem eq_on_block {K : ℕ → ℕ} (h : IsKolakoski K)
    {n i : ℕ} (hn : 1 ≤ n)
    (hstart : kolakoskiBlockStart K n ≤ i)
    (hend : i < kolakoskiBlockStart K n + K n) :
    K i = if n % 2 = 1 then 1 else 2 :=
  h.2.2 n hn i hstart hend

theorem two {K : ℕ → ℕ} (h : IsKolakoski K) : K 2 = 2 := by
  have hpositive : 0 < K 2 := by
    rcases h.value_eq_one_or_two (n := 2) (by decide) with hK | hK <;> simp [hK]
  have hblock := h.eq_on_block (n := 2) (i := kolakoskiBlockStart K 2)
    (by decide) le_rfl (Nat.lt_add_of_pos_right hpositive)
  simpa [kolakoskiBlockStart, h.one] using hblock

theorem three {K : ℕ → ℕ} (h : IsKolakoski K) : K 3 = 2 := by
  have hblock := h.eq_on_block (n := 2) (i := 3) (by decide)
    (by simp [kolakoskiBlockStart, h.one])
    (by simp [kolakoskiBlockStart, h.one, h.two])
  simpa using hblock

theorem four {K : ℕ → ℕ} (h : IsKolakoski K) : K 4 = 1 := by
  have hblock := h.eq_on_block (n := 3) (i := 4) (by decide)
    (by simp [kolakoskiBlockStart, h.one, h.two])
    (by simp [kolakoskiBlockStart, h.one, h.two, h.three])
  simpa using hblock

end IsKolakoski

end MetaMathlibExt
