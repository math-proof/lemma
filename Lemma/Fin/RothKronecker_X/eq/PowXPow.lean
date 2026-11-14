import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronecker_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [Field K]
  (D : ℕ) (h : Fin m) :
-- imply
  rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
    Polynomial.X ^ D ^ (h : ℕ) := by
-- proof
  simp [rothKronecker]


-- updated on 2026-11-13
-- created on 2026-10-21
