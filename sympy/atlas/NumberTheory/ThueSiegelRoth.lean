/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThueSiegelRoth.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import sympy.atlas.NumberTheory.RothAuxiliary
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

/-!
This file proves Roth's theorem for rational approximation of real algebraic irrationals.
-/

namespace MathlibExt.NumberTheory.ThueSiegelRothWanted

/--
For irrational real algebraic `α : ℝ` and any `ε > 0`, only finitely many `q : ℚ` satisfy `|α - q|
< 1 / (q.den : ℝ) ^ (2+ε)` via `Real.rpow`. Source: K. F. Roth, Rational approximations to
algebraic numbers, Mathematika 2 (1955) 1–20; predecessors Thue 1909 and Siegel 1921; textbook in
Schmidt, Diophantine Approximation

Proves `Wanted` entry `thue_siegel_roth`.

Proof: The proof constructs Siegel's auxiliary polynomial, bounds its index at rational
approximation points by a Taylor estimate, and contradicts the inductive Roth lemma.
-/
theorem thue_siegel_roth :
    ∀ (α : ℝ), IsAlgebraic ℚ α → Irrational α →
      ∀ (ε : ℝ), 0 < ε →
        Set.Finite { q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε) } := by
  intro α hα hαi ε hε
  let e := min ε 1
  have he : 0 < e := lt_min hε zero_lt_one
  have heone : e ≤ 1 := min_le_right _ _
  have hsmall :
      Set.Finite {q : ℚ |
        |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + e)} := by
    have hcore :=
      MathlibExt.NumberTheory.RothAuxiliary.finite_of_divisible_approximations
        α hα e he heone
        (∅ : Finset (Fin 0)) (fun i ↦ Fin.elim0 i)
        (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
        (by simp) (by simp) (by positivity)
    simpa using hcore
  refine hsmall.subset ?_
  intro q hq
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hexp : 2 + e ≤ 2 + ε := by
    dsimp [e]
    linarith [min_le_left ε 1]
  have hpow : Real.rpow (q.den : ℝ) (2 + e) ≤
      Real.rpow (q.den : ℝ) (2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hden hexp
  exact hq.trans_le (one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (by positivity) _) hpow)

end MathlibExt.NumberTheory.ThueSiegelRothWanted
