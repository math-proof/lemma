import Mathlib
import sympy.Basic


/--
[Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le.lean)
-/
@[path]
private lemma main
  [CommRing B] [IsNoetherianRing B]
  {I : Ideal B}
  {P : Ideal B} [P.IsPrime]
-- given
  (hI : I ≤ I ^ 2)
  (hIP : I ≤ P) :
-- imply
  ∃ f : B, f ∉ P ∧ ∀ a ∈ I, f * a = 0 := by
-- proof
  classical
  have hfg : I.FG := (isNoetherianRing_iff_ideal_fg B).1 inferInstance I
  have hle : I ≤ I • I := by
    intro a ha
    have := hI ha
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I I hfg hle
  refine ⟨r, ?_, fun a ha => ?_⟩
  · intro hrP
    have h1 : r - (r - 1) ∈ P := P.sub_mem hrP (hIP hr1)
    rw [sub_sub_cancel] at h1
    exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top inferInstance) h1
  · have := hr a ha
    rwa [smul_eq_mul] at this


-- created on 2026-10-05
