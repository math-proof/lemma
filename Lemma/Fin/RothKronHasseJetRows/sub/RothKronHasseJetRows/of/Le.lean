import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
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


-- updated on 2026-11-13
-- created on 2026-10-21
