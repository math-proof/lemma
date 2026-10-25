/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MultisetEulerianNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
/-!
# Eulerian numbers of multiset permutations

This file formalizes the descent-count definition in Dzhumadil'daev and
Yeliussizov, *Power Sums of Binomial Coefficients*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>.
-/


namespace MetaMathlibExt

/-- The source-convention descent number of a word: its ordinary descents,
plus the terminal descent position. -/
def multisetDescentNumber {m K : ℕ} (w : Fin K → Fin m) : ℕ :=
  ((Finset.range K).filter fun j =>
    if h : j + 1 < K then w ⟨j, Nat.lt_of_succ_lt h⟩ > w ⟨j + 1, h⟩ else False).card + 1

/-- A word is a permutation of the multiset having `k i` copies of each
letter `i`. -/
def IsMultisetPermutation {m K : ℕ} (k : Fin m → ℕ) (w : Fin K → Fin m) : Prop :=
  ∀ i, ((Finset.univ : Finset (Fin K)).filter fun j => w j = i).card = k i

end MetaMathlibExt
