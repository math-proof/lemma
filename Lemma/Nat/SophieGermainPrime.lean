import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.SophieGermainPrime
open Nat


namespace Nat

/--
[isSophieGermainPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
lemma isSophieGermainPrime_iff
  {p : ℕ} :
-- imply
  IsSophieGermainPrime p ↔ Nat.Prime p ∧ Nat.Prime (2 * p + 1) :=
-- proof
  Iff.rfl

end Nat

namespace Nat

/--
[IsSophieGermainPrime.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
lemma IsSophieGermainPrime.prime
  {p : ℕ}
-- given
  (h : IsSophieGermainPrime p) :
-- imply
  Nat.Prime p :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsSophieGermainPrime.prime_two_mul_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
lemma IsSophieGermainPrime.prime_two_mul_add_one
  {p : ℕ}
-- given
  (h : IsSophieGermainPrime p) :
-- imply
  Nat.Prime (2 * p + 1) :=
-- proof
  h.2

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
