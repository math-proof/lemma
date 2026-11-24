module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[roth_eval₂_rat_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) (q : Fin m → ℚ) :
-- imply
  ((MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P : ℚ) : ℝ) =
    MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P := by
-- proof
  change (algebraMap ℚ ℝ) (MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 2


-- created on 2026-10-21
-- updated on 2026-11-15
