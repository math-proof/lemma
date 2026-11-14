import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.RothAuxiliary.Part7


namespace MathlibExt.NumberTheory.ThueSiegelRothWanted

/--
[thue_siegel_roth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThueSiegelRoth.lean)
-/
@[path]
lemma thue_siegel_roth
  :
-- imply
  ∀ (α : ℝ), IsAlgebraic ℚ α → Irrational α →
    ∀ (ε : ℝ), 0 < ε →
    Set.Finite { q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε) } := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-11-13
