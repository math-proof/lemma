import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.VonSzilySuperCatalan
open scoped BigOperators
open MetaMathlibExt


/--
[von_szily_super_catalan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma von_szily_super_catalan_identity_eq
  {m n : ℕ} :
-- imply
  (((2 * m).factorial * (2 * n).factorial /
    (m.factorial * n.factorial * (m + n).factorial) : ℕ) : ℤ) =
    ∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min (m : ℤ) (n : ℤ)),
    (-1 : ℤ) ^ k.natAbs *
    (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
    (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ) := by
-- proof
  apply MetaMathlibExt.von_szily_super_catalan_identity m n


-- created on 2026-10-20
