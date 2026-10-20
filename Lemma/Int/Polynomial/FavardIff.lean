import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.FavardIff
open _root_.Polynomial
open MetaMathlibExt


/--
[favard_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/FavardIff.lean)
-/
@[path]
private lemma favard_iff_eq
  [Field R]
  {p : ℕ → Polynomial R}
-- given
  (hmonic : ∀ n, (p n).Monic) :
-- imply
  Polynomial.IsFormallyOrthogonal p ↔
    ∃ (α β : ℕ → R), (∀ n, β (n + 1) ≠ 0) ∧ p 0 = 1 ∧
    p 1 = Polynomial.X - Polynomial.C (α 0) ∧
    ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
    p (n + 1) - Polynomial.C (β (n + 1)) * p n := by
-- proof
  apply MetaMathlibExt.favard_iff p hmonic


-- created on 2026-10-20
