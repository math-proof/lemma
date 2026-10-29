import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.QuadraticCharacterAux


namespace MetaMathlibExt

/--
[jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridge.lean)
-/
@[path]
lemma jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
  (D : ℤ)
  (p : ℕ)
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hpos : 0 < D)
  (h0 : D % 4 = 1) :
-- imply
  jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
-- proof
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hcast : ((D.natAbs : ℕ) : ℤ) = D := by
    rw [Int.natCast_natAbs, abs_of_pos hpos]
  have hNmod : D.natAbs % 4 = 1 := by omega
  have hrec :=
    jacobiSym.quadratic_reciprocity_one_mod_four hNmod hp_odd
  have hKR : kroneckerSym D p = jacobiSym D p :=
    kroneckerSym_eq_jacobiSym_of_prime_ne_two D p hp hp2
  rw [hKR]
  conv_rhs => rw [← hcast]
  exact hrec.symm

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-29
