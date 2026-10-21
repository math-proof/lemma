import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma faithfullyFlat_adicCompletion
  (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
  -- imply
  Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  -- proof
  let _ : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  have hm' : m = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hm)
  subst hm'
  intro htop
  have hle : (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := by
    have := AdicCompletion.pow_smul_top_le_ker_eval (I := maximalIdeal R) (M := R) 1
    simpa using this
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  rw [hle] at hsurj
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk 1)
  simp only [LinearMap.zero_apply] at hx
  have h1 : (1 : R) ∈ (maximalIdeal R) ^ 1 • (⊤ : Submodule R R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hx]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
  apply (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/--
[IsLocalRing_comap_map_adicCompletion_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_comap_map_adicCompletion_eq.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (I : Ideal R) :
  -- imply
  (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  -- proof
  let _ := faithfullyFlat_adicCompletion R
  apply Ideal.comap_map_eq_self_of_faithfullyFlat I


-- created on 2026-10-20
