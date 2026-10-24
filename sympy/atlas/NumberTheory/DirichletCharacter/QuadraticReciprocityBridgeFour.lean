/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean -/

import Lemma.Nat.DirichletCharacter.QuadraticReciprocityThreeOdd
/-! Even-family reduction for the reciprocity bridge.

At an odd `p` the factor `4` contributes nothing to the Jacobi symbol,
so `kroneckerSym (4 * m) p` reduces to `m`; chaining this with the `m % 4 = 3`
bridge (applied to `m`) closes the `m % 4 = 3` subcase of the second
`IsFundamentalDiscriminant` disjunct for prime and composite odd denominators
alike. The one-power-of-two version is included for the `m % 4 = 2` subcase,
which has no public bridge lemma here; `quadraticDirichletCharacter` in
`MathlibExt.NumberTheory.DirichletCharacter.QuadraticDirichletCharacter` closes that
subcase and completes the assembly over `IsFundamentalDiscriminant`.
-/

namespace MetaMathlibExt

/-- Even `m % 4 = 3` subcase for odd `p`: reduce `4 * m` to `m`, identify
`kroneckerSym` with `jacobiSym` at odd denominators, then apply the `D % 4 = 3`
bridge to `m` itself. Covers prime and composite odd denominators alike. -/
theorem
    chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    (m : ℤ) (p : ℕ) (hp_odd : Odd p) (h3 : m % 4 = 3) :
    (ZMod.χ₄ p : ℤ) * jacobiSym (p : ℤ) m.natAbs = kroneckerSym (4 * m) p := by
  have hKR4 : kroneckerSym (4 * m) p = jacobiSym (4 * m) p :=
    kroneckerSym_eq_jacobiSym_of_odd (4 * m) p hp_odd
  have h4red : jacobiSym (4 * m) p = jacobiSym m p :=
    jacobiSym_four_mul_of_odd m p hp_odd
  have hKRm : kroneckerSym m p = jacobiSym m p :=
    kroneckerSym_eq_jacobiSym_of_odd m p hp_odd
  have hBridge :
      (ZMod.χ₄ p : ℤ) * jacobiSym (p : ℤ) m.natAbs = kroneckerSym m p :=
    chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
      m p hp_odd h3
  rw [hKR4, h4red, ← hKRm]
  exact hBridge

end MetaMathlibExt
