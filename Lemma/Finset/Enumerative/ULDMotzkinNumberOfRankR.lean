import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
open MetaMathlibExt
open ULDMotzkin


namespace MetaMathlibExt.ULDMotzkin

/--
[uldMotzkinNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean)
-/
@[path]
lemma uldMotzkinNumber_eq_card
  {r : ℕ}
  {u : Fin r → ℕ}
  {l : ℕ}
  {d : Fin r → ℕ}
  {n : ℕ}
-- given
  (hr : 1 ≤ r) :
-- imply
  uldMotzkinNumber r u l d hr n =
    Fintype.card { p : Fin n → ULDMotzkinStep r u l d //
    IsMotzkinPath r u l d hr n p } :=
-- proof
  rfl

end MetaMathlibExt.ULDMotzkin


-- created on 2026-10-20
-- updated on 2026-10-23
