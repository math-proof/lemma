import Mathlib
import sympy.Basic

open IntermediateField

/--
[IntermediateField_adjoin_rootsOfUnity_padic_mono](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_adjoin_rootsOfUnity_padic_mono.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {K : IntermediateField ℚ_[q] (PadicAlgCl q)}
  {N N' : ℕ}
-- given
  (h : N ∣ N') :
-- imply
  IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤
      IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1} := by
-- proof
  apply IntermediateField.adjoin.mono
  intro ζ hζ
  obtain ⟨k, rfl⟩ := h
  obtain ⟨c, hc⟩ : q ^ N - 1 ∣ q ^ (N * k) - 1 := by
    rw [pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (q ^ N) k
  change ζ ^ (q ^ (N * k) - 1) = 1
  rw [hc, pow_mul, show ζ ^ (q ^ N - 1) = 1 from hζ, one_pow]


-- created on 2026-10-05
