import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
-- imply
  Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
-- proof
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => ?_⟩
  have hle : (I • ⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤ (maximalIdeal R) ^ 1 • ⊤ := by
    rw [pow_one]; exact Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
  rw [htop, top_le_iff, AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _)] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  have hne : ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R) ≠ ⊤ := by
    rw [pow_one, smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R)) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨q, hq⟩ := exists_ne (0 : R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R))
  obtain ⟨x, rfl⟩ := hsurj q
  have hx : x ∈ LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := hle ▸ Submodule.mem_top
  exact hq (LinearMap.mem_ker.mp hx)


-- created on 2026-10-05
