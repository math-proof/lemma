import Mathlib
import sympy.Basic
import Def.NumberTheory.DirichletCharacter.Quadratic
open MetaMathlibExt


namespace MetaMathlibExt

/--
[kroneckerSym_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
lemma kroneckerSym_zero
  {D : ℤ} :
-- imply
  kroneckerSym D 0 = if D.natAbs = 1 then 1 else 0 := by
-- proof
  simp [kroneckerSym]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
lemma kroneckerSym_one
  {D : ℤ} :
-- imply
  kroneckerSym D 1 = 1 := by
-- proof
  simp [kroneckerSym]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerAtPrime_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
lemma kroneckerAtPrime_two
  {D : ℤ} :
-- imply
  kroneckerAtPrime D 2 = kroneckerAtTwo D := by
-- proof
  simp [kroneckerAtPrime]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
lemma kroneckerSym_two
  {D : ℤ} :
-- imply
  kroneckerSym D 2 = kroneckerAtTwo D := by
-- proof
  have hprime : Nat.Prime 2 := Nat.prime_two
  have hlist : Nat.primeFactorsList 2 = [2] :=
    Nat.primeFactorsList_prime hprime
  rw [kroneckerSym, ite_eq_right (by decide), hlist]
  simp [kroneckerAtPrime]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
lemma kroneckerSym_prime
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  kroneckerSym D p = kroneckerAtPrime D p := by
-- proof
  have hne : p ≠ 0 := hp.ne_zero
  have hlist : p.primeFactorsList = [p] := Nat.primeFactorsList_prime hp
  rw [kroneckerSym, ite_eq_right hne, hlist]
  simp

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
