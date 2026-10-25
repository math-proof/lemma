/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/OddLichtenbergNumbers.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Odd Lichtenberg numbers

Formalizes the odd Lichtenberg numbers (OEIS A002450).
-/


namespace MetaMathlibExt

/-- Odd Lichtenberg numbers (OEIS A002450): the sequence of positive `3`-key
distances `(1 / 3) * M_{2 * k} = ℓ_{2 * k - 1} = 1, 5, 21, 85, …`, described as
the self-generating sequence for seed `1` with generating function set
`{k ↦ 4 * k + 1}`, so `a 0 = 1` and `a (n + 1) = 4 * a n + 1`.

Concept `jis_sem_21a46571c2d8f3f53edb5728` (`odd Lichtenberg numbers`);
required clause from stable statement `jis_e2a7cb75f919d56e388fa0b1` in
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Hinz/hinz5.tex`. -/
def oddLichtenberg : ℕ → ℕ
  | 0 => 1
  | n + 1 => 4 * oddLichtenberg n + 1

end MetaMathlibExt
