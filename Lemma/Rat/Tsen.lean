import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Tsen
open MathlibExt.FieldTheory.TsenWanted


/--
[tsen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Tsen.lean)
-/
@[path]
private lemma tsen_eq
  :
-- imply
  ∀ (k : Type*) [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (RatFunc k)),
    f.IsHomogeneous d → 0 < d → d < n →
    ∃ (x : Fin n → RatFunc k), (∃ i, x i ≠ 0) ∧ MvPolynomial.eval x f = 0 := by
-- proof
  apply MathlibExt.FieldTheory.TsenWanted.tsen


-- created on 2026-10-20
