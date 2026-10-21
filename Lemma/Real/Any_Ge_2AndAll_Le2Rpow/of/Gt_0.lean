import Mathlib
import sympy.Basic


/--
[roth_exists_rpow_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q : ℕ, Q ≤ q → (2 : ℝ) ≤ Real.rpow q lam := by
-- proof
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ lam :=
    Filter.tendsto_atTop.1 (tendsto_rpow_atTop hlam) 2
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ := exists_nat_ge A
  refine ⟨max 2 N, le_max_left _ _, fun q hq ↦ ?_⟩
  apply hA q
  exact hN.trans (by exact_mod_cast (le_trans (le_max_right 2 N) hq))


-- created on 2026-10-21
