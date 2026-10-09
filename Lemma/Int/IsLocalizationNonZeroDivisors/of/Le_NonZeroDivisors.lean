import Mathlib
import sympy.Basic


/--
[IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors.lean)
-/
@[path]
private lemma main
  {B F : Type*} [CommRing B] [CommRing F] [Algebra B F] [IsArtinianRing F]
  {M : Submonoid B} [IsLocalization M F]
-- given
  (hM : M ≤ nonZeroDivisors B) :
-- imply
  IsLocalization (nonZeroDivisors B) F := by
-- proof
  refine IsLocalization.of_le M (nonZeroDivisors B) hM fun r hr => ?_
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro u hu
  obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective M u
  have h1 : algebraMap B F (x * r) = 0 := by
    have h := congrArg (fun z => z * algebraMap B F (m : B)) hu
    simp only [zero_mul] at h
    rw [map_mul, ← IsLocalization.mk'_spec F x m]
    calc IsLocalization.mk' F x m * algebraMap B F ↑m * algebraMap B F r
        = IsLocalization.mk' F x m * algebraMap B F r * algebraMap B F ↑m := by ring
      _ = 0 := h
  obtain ⟨m', hm'⟩ := (IsLocalization.map_eq_zero_iff M F _).1 h1
  have hx : (m' : B) * x = 0 := by
    have h2 : (m' : B) * x * r = 0 := by rw [mul_assoc]; exact hm'
    exact (mem_nonZeroDivisors_iff_right.1 hr) _ h2
  exact (IsLocalization.mk'_eq_zero_iff x m).2 ⟨m', hx⟩


-- created on 2026-10-05
