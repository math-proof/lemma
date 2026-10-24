import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PellLucasNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pellLucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
lemma pellLucas_zero
  :
-- imply
  pellLucas 0 = 2 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pellLucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
lemma pellLucas_one
  :
-- imply
  pellLucas 1 = 2 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pellLucas_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean)
-/
@[path]
lemma pellLucas_add_two
  {n : Nat} :
-- imply
  pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
