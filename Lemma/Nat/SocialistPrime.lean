import Mathlib
import sympy.Basic
import Def.NumberTheory.SocialistPrime
open Nat


namespace Nat

/--
[IsSocialistPrime.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
lemma IsSocialistPrime.prime
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  Nat.Prime p :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsSocialistPrime.five_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
lemma IsSocialistPrime.five_lt
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  5 < p :=
-- proof
  h.2.1

end Nat

namespace Nat

/--
[IsSocialistPrime.pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
lemma IsSocialistPrime.pairwise
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  Set.Pairwise (Set.Icc 2 (p - 1)) (fun k l => k.factorial % p ≠ l.factorial % p) :=
-- proof
  h.2.2

end Nat

namespace Nat

/--
[IsSocialistPrime.factorial_mod_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
lemma IsSocialistPrime.factorial_mod_ne
  {p a b : ℕ}
-- given
  (h : IsSocialistPrime p)
  (ha : a ∈ Set.Icc 2 (p - 1))
  (hb : b ∈ Set.Icc 2 (p - 1))
  (hab : a ≠ b) :
-- imply
  a.factorial % p ≠ b.factorial % p :=
-- proof
  h.pairwise ha hb hab

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
