import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PellLucasNumber
open MetaMathlibExt


/--
[pellLucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
private lemma pellLucas_zero_eq
  :
-- imply
  pellLucas 0 = 2 := by
-- proof
  apply MetaMathlibExt.pellLucas_zero

/--
[pellLucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
private lemma pellLucas_one_eq
  :
-- imply
  pellLucas 1 = 2 := by
-- proof
  apply MetaMathlibExt.pellLucas_one

/--
[pellLucas_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
private lemma pellLucas_add_two_eq
  {n : Nat} :
-- imply
  pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n := by
-- proof
  apply MetaMathlibExt.pellLucas_add_two n


-- created on 2026-10-20
