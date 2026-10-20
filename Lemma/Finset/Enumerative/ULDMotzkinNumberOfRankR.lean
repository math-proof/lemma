import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
open MetaMathlibExt
open ULDMotzkin


/--
[uldMotzkinNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean)
-/
@[path]
private lemma uldMotzkinNumber_eq_card_eq
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
    IsMotzkinPath r u l d hr n p } := by
-- proof
  apply MetaMathlibExt.ULDMotzkin.uldMotzkinNumber_eq_card r u l d hr n


-- created on 2026-10-20
