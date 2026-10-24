import Mathlib
import sympy.Basic


namespace CoxeterGroup

/--
[list_prod_rotate_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CyclicRotation.lean)
-/
@[path]
lemma list_prod_rotate_eq_one
  [Group G]
  {w : List G}
  {k : ℕ}
-- given
  (hw : w.prod = 1) :
-- imply
  (w.rotate k).prod = 1 :=
-- proof
  List.prod_rotate_eq_one_of_prod_eq_one hw k

end CoxeterGroup


-- created on 2026-10-23
