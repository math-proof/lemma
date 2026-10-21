import Mathlib
import Lemma.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_exists_nonzero_hasse_of_not_vanishesBelow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {P : MvPolynomial (Fin m) ℚ}
  {x : Fin m → ℚ}
  {r : Fin m → ℕ}
  {T : ℝ}
-- given
  (h : ¬rothMvVanishesBelow P x r T) :
-- imply
  ∃ i : RothMvIndex m, rothMvWeight r i < T ∧
    MvPolynomial.eval x (rothMvHasse i P) ≠ 0 := by
-- proof
  rw [rothMvVanishesBelow] at h
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  refine ⟨i, hi, ?_⟩
  simpa [CoeffRothTranslateM.eq.EvalRothMvHasse] using hne


-- created on 2026-10-21
