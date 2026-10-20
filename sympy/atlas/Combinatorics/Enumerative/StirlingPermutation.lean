/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingPermutation.lean -/

import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

/-- Stirling permutation of order `n` (concept `jis_sem_2caeda2867f94a2afc83e068`,
statement `jis_e248733f0c7bd4348abb29fb`,
source `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex`):
a word `w : Fin (2 * n) → ℕ` with values in `{1, …, n}`, each value occurring
exactly twice, such that every value appearing between the two instances of `i`
is strictly greater than `i`. -/
def IsStirlingPermutation (n : ℕ) (w : Fin (2 * n) → ℕ) : Prop :=
  (∀ k, w k ∈ Finset.Icc 1 n) ∧
  (∀ v ∈ Finset.Icc 1 n,
    Finset.card (Finset.univ.filter (fun k => w k = v)) = 2) ∧
  ∀ i ∈ Finset.Icc 1 n, ∀ a b c : Fin (2 * n),
    a < b → b < c → w a = i → w c = i → i < w b

/-- The set `Q_n` of Stirling permutations of order `n`
(concept `jis_sem_2caeda2867f94a2afc83e068`,
statement `jis_e248733f0c7bd4348abb29fb`,
source `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex`),
written as words `w(1) w(2) ⋯ w(2n)`. -/
def StirlingPermSet (n : ℕ) : Set (Fin (2 * n) → ℕ) :=
  {w | IsStirlingPermutation n w}

end MetaMathlibExt
