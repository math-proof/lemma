/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EvenTableWeight.lean -/

import Def.Combinatorics.Enumerative.ColumnWeight
import Structure.Combinatorics.Enumerative.EvenTableWeight
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

/-- The weight of an even table is the product of its column weights. -/
def evenTableWeight {M : Type*} [CommMonoid M] {k n : ℕ}
    (factor : ℕ → M) (t : EvenTable k n) : M :=
  ∏ j, columnWeight n factor (List.ofFn fun i => t.entries i j)

end MetaMathlibExt
