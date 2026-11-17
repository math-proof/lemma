module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronHasseJetRows_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothKronHasseJetRows.sub.RothKronHasseJetRows.of.Le
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
