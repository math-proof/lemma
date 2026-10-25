import Mathlib
import sympy.Basic
import Lemma.ModularCurve.CuspidalClass
import Lemma.Int.P2MUtil

open ModularCurve AlgebraicCurve
open scoped Pointwise

/--
[ModularCurve_frickeInvolutionBar_coeffEmb_qExpand](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.lean)
-/
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {a b : ℕ} [NeZero a] [NeZero b]
-- given
  (h : IsFrickeAutFull N (frickeInvolutionFull N))
  (hab : a * b = N) :
-- imply
  frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by
-- proof
  rw [frickeInvolutionBar_def]
  refine (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)
    ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩).trans (Subtype.ext ?_)
  change coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull N ⟨qExpand ℚ a jq, _⟩ : modularFunctionFieldFull N) :
    LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq)
  rw [h a b hab ‹NeZero a› ‹NeZero b›]


-- created on 2026-10-23
