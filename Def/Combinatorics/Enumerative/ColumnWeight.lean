/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ColumnWeight.lean -/

import Mathlib.Algebra.BigOperators.Fin
open scoped BigOperators

/-!
# Column weights

This definition is used by Dominik Beck, Zelin Lv, and Aaron Potechin,
*The Sixth Moment of Random Determinants*, Journal of Integer Sequences 26
(2023), Article 23.6.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Lv/lv3.tex>.
-/


namespace MetaMathlibExt

/-- The weight of a column is the product, over its possible entries, of a
factor determined by that entry's multiplicity.

Stable source identifiers: concept `jis_sem_a5942561d609e6dce822e138`,
statement `jis_7896cefc507363fdee018052`.
-/
def columnWeight (n : ℕ) {M : Type*} [CommMonoid M]
    (factor : ℕ → M) (column : List (Fin n)) : M :=
  ∏ j, factor ((column.filter (· = j)).length)

end MetaMathlibExt
