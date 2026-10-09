import sympy.Basic
import Mathlib

open IsLocalRing

/-! Port of FLT ComplUniq from
S_AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing. -/
namespace FltWs21
namespace ComplUniq

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem map_mem_pow_smul_top (e : AdicCompletion I R →+* AdicCompletion I R)
    (he : ∀ r : R, e (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) r) (n : ℕ)
    {x : AdicCompletion I R} (hx : x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R))) :
    e x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [Algebra.smul_def, map_mul, he, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

theorem apply_eq_self_of_forall_apply_algebraMap (hI : I.FG) (e : AdicCompletion I R →+* AdicCompletion I R)
    (he : ∀ r : R, e (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) r)
    (x : AdicCompletion I R) : e x = x := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have hval : (algebraMap R (AdicCompletion I R) r).val n = x.val n := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.of_apply]
    exact hr
  have hmem : x - algebraMap R (AdicCompletion I R) r ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, AdicCompletion.eval_apply,
      AdicCompletion.eval_apply, hval, sub_self]
  have hmem' := map_mem_pow_smul_top I e he n hmem
  rw [map_sub, he, AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, sub_eq_zero,
    AdicCompletion.eval_apply, AdicCompletion.eval_apply, hval] at hmem'
  exact hmem'

end ComplUniq
end FltWs21

/--
[AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing.lean)
-/
@[path]
private lemma main
  {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
-- given
  (e₁ e₂ : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R) (h : ∀ r : R, e₁ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)
      = e₂ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) :
-- imply
  e₁ = e₂ := by
-- proof
  have hI : (IsLocalRing.maximalIdeal R).FG := IsNoetherian.noetherian _
  apply RingEquiv.ext
  intro x
  have key := FltWs21.ComplUniq.apply_eq_self_of_forall_apply_algebraMap (IsLocalRing.maximalIdeal R) hI
    ((e₂.symm : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* _).toRingHom.comp e₁.toRingHom)
    (fun r => by
      show e₂.symm (e₁ (algebraMap R _ r)) = algebraMap R _ r
      rw [h r, RingEquiv.symm_apply_apply]) x
  have key' : e₂.symm (e₁ x) = x := key
  have := congrArg e₂ key'
  rwa [RingEquiv.apply_symm_apply] at this

-- created on 2026-10-09
