import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronHasseJetRows_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ}
  (D : ℕ) (f : Fin k → MvPolynomial (Fin m) ℚ)
  {s t : ℕ}
-- given
  (hst : s ≤ t) :
-- imply
  rothKronHasseJetRows D f s ⊆ rothKronHasseJetRows D f t := by
-- proof
  rintro v ⟨i, hi, rfl⟩
  exact ⟨i, hi.trans hst, rfl⟩


-- created on 2026-10-21
