/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridge.lean -/

import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticCharacterAux
/-! Easy branch of the reciprocity bridge. -/

namespace MetaMathlibExt

/-- Reciprocity bridge for positive `D` with `D % 4 = 1` at an odd
prime `p` (`p` prime with `p ≠ 2`).
The negative and `D = 4 * m` branches are not covered. `h1` is a
truth condition, not just a proof boundary: at `(D, p) = (3, 7)`,
`jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs = 1` while
`kroneckerSym (3 : ℤ) 7 = -1`, so the conclusion fails without `h1`.
For `hpos` no counterexample was found: at `D = -3` both sides agree
for `p = 5, 7, 11`, and whether `hpos` is necessary is open. `hp`
and `hp2` are retained as stated; no proof dropping them is claimed
here. The unconditional step `kroneckerSym D p = jacobiSym D p` is
reused from `kroneckerSym_eq_jacobiSym_of_prime_ne_two`. -/
theorem jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
    (D : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpos : 0 < D)
    (h1 : D % 4 = 1) :
    jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
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
