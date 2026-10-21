import Mathlib
import sympy.Basic


/--
[roth_exists_rpow_threshold_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (C : ℝ)
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → C ≤ Real.rpow q lam := by
-- proof
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, C ≤ x ^ lam :=
    Filter.tendsto_atTop.1 (tendsto_rpow_atTop hlam) C
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨Q, hQ⟩ := exists_nat_ge A
  exact ⟨Q, fun q hq ↦ hA q (hQ.trans (by exact_mod_cast hq))⟩


-- created on 2026-10-21
