/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EvenTableWeight.lean -/

import Def.Combinatorics.Enumerative.ColumnWeight
open scoped BigOperators

/-!
# Weights of even tables

This file defines even tables and their weights as used in the combinatorial expansion of random
determinant moments.

The source is Dominik Beck, Zelin Lv, and Aaron Potechin, *The Sixth Moment of Random
Determinants*, Journal of Integer Sequences 26 (2023), Article 23.6.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Lv/lv3.tex>, SHA-256
`b7561d53b71f40dc02aa6a65b56e1c93c202ea58e9067ccbe04a021a9dee97b0`.

Provenance: statement `jis_27d3ea8c4aa1d31860d82adf`, semantic concept
`jis_sem_fb63c6b5f1a68ced5b0d9660`.
-/


namespace MetaMathlibExt

/-- An even `k × n` table: `k` is even, every row is a permutation of `Fin n`, and every
value occurring in a column has even multiplicity. -/
structure EvenTable (k n : ℕ) where
  entries : Fin k → Fin n → Fin n
  isEven : Even k
  rowBijective : ∀ i, Function.Bijective (entries i)
  colEven : ∀ (j : Fin n) (v : Fin n), (∃ i, entries i j = v) →
    Even ((List.ofFn fun i => entries i j).count v)

end MetaMathlibExt
