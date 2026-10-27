import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[span_nat_prime_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/LinearGroupFiniteness.lean)
-/
@[path]
private lemma main
  (p : ℕ)
  (hp : p.Prime) :
-- imply
  (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal := by
-- proof
  have hP : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hI : Irreducible ((p : ℤ)) := hP.irreducible
  exact PrincipalIdealRing.isMaximal_of_irreducible hI


-- created on 2026-10-20
-- updated on 2026-10-26
