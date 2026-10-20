import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion
open MetaMathlibExt


/--
[r3_legendre_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3_legendre_recursion_eq
  {p n α : ℕ} [Fact (Nat.Prime p)]
-- given
  (hp3 : 3 ≤ p)
  (hn : 1 ≤ n) :
-- imply
  (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
    (((((p : ℤ) ^ (α + 1) - 1) / ((p : ℤ) - 1)) -
    legendreSym p (-(n : ℤ)) *
    (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1))) *
    Nat.threeSquareRepresentationCount n -
    (p : ℤ) * (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1)) *
    (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) := by
-- proof
  apply MetaMathlibExt.r3_legendre_recursion hp3 hn


-- created on 2026-10-20
