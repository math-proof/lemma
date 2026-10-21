import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvHasse_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (i j : RothMvIndex m) (c : R) :
-- imply
  rothMvHasse i (MvPolynomial.monomial j c) =
    MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c) := by
-- proof
  simp [rothMvHasse]


-- created on 2026-10-21
