import Mathlib
import sympy.Basic


/--
[IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank.lean)
-/
@[main]
private lemma main
  {k K : Type*} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  {p : ℕ} [Fact p.Prime] :
-- imply
  ∃ E : IntermediateField k K, IsPGroup p (K ≃ₐ[↥E] K) ∧ ¬ p ∣ Module.finrank k ↥E := by
-- proof
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p (K ≃ₐ[k] K)))
  refine ⟨IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)), ?_, ?_⟩
  ·
    have hfix : (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))).fixingSubgroup = (P : Subgroup (K ≃ₐ[k] K)) :=
      IntermediateField.fixingSubgroup_fixedField (P : Subgroup (K ≃ₐ[k] K))
    let e : ↥(P : Subgroup (K ≃ₐ[k] K)) ≃* (K ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)))] K) :=
      (MulEquiv.subgroupCongr hfix.symm).trans
        (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))))
    exact IsPGroup.of_surjective P.isPGroup' e.toMonoidHom e.surjective
  ·
    have hEK : Module.finrank ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K = Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) :=
      IntermediateField.finrank_fixedField_eq_card (P : Subgroup (K ≃ₐ[k] K))
    have htower := Module.finrank_mul_finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K
    have hG : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
    have hPi := (P : Subgroup (K ≃ₐ[k] K)).card_mul_index
    have hcard : 0 < Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) := Nat.card_pos
    have hidx : Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) = (P : Subgroup (K ≃ₐ[k] K)).index := by
      apply Nat.eq_of_mul_eq_mul_left hcard
      calc Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) * Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)))
          = Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) *
              Module.finrank ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K := by rw [mul_comm, hEK]
        _ = Module.finrank k K := htower
        _ = Nat.card (K ≃ₐ[k] K) := hG.symm
        _ = Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) * (P : Subgroup (K ≃ₐ[k] K)).index := hPi.symm
    rw [hidx]
    exact P.not_dvd_index


-- created on 2026-10-05
