import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.FavardForward
open _root_.Polynomial
open MetaMathlibExt


/--
[favard_forward](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/FavardForward.lean)
-/
@[path]
private lemma favard_forward_eq
  [Field R]
  {p : ℕ → Polynomial R}
-- given
  (hmonic : ∀ n, (p n).Monic)
  (horth : Polynomial.IsFormallyOrthogonal p) :
-- imply
  ∃ (α β : ℕ → R), (∀ n, β (n + 1) ≠ 0) ∧ p 0 = 1 ∧
    p 1 = Polynomial.X - Polynomial.C (α 0) ∧
    ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
    p (n + 1) - Polynomial.C (β (n + 1)) * p n := by
-- proof
  apply MetaMathlibExt.favard_forward p hmonic horth


-- created on 2026-10-20
