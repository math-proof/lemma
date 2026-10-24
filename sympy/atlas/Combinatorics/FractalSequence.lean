/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FractalSequence.lean -/

import Mathlib.Data.Set.Card

namespace MetaMathlibExt

/-- A regular Kimberling fractal sequence, represented together with its exact
occurrence-position array.

Source JIS VOL25/Kimberling,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.tex>, lines 103–219;
concept `jis_term_9b50b937a4f55a665e8d81fb`.

Source positive value `i + 1` is represented directly as the natural `i + 1`,
and `pos i j` is the zero-based position of its `j`-th occurrence. -/
structure FractalSequence where
  /-- The positive-valued sequence. -/
  seq : ℕ → ℕ
  seq_pos : ∀ n, 0 < seq n
  /-- `pos i j` is the zero-based index of the `j`-th occurrence of value `i + 1`. -/
  pos : ℕ → ℕ → ℕ
  /-- Occurrence positions for a fixed value increase strictly. -/
  pos_strict : ∀ i, StrictMono (pos i)
  /-- Every recorded occurrence position contains the corresponding value. -/
  pos_sound : ∀ i j, seq (pos i j) = i + 1
  /-- Every occurrence of a value appears in its position row. -/
  pos_complete : ∀ i n, seq n = i + 1 → ∃ j, pos i j = n
  /-- Source condition (F2), shifted to zero-based value indices. -/
  cond_F2 : ∀ n i, seq n = i + 2 → ∃ m, m < n ∧ seq m = i + 1
  /-- Source condition (F3): exactly one smaller-value position lies strictly
  between consecutive positions of a larger value. -/
  cond_F3 : ∀ h i j, h < i → ∃! k, pos i j < pos h k ∧ pos h k < pos i (j + 1)
  /-- Regularity: every column of the position array increases strictly. -/
  pos_column_strict : ∀ j, StrictMono (fun i => pos i j)
end MetaMathlibExt
