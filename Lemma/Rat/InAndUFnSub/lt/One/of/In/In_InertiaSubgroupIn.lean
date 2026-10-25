import Mathlib
import sympy.Basic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil


/--
[ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.lean)
-/
@[path]
private lemma main
  {K L : Type*} [Field K] [Field L] [Algebra K L]
  {A : ValuationSubring L}
  {σ : L ≃ₐ[K] L}
  {a : L}
-- given
  (hσ : σ ∈ A.inertiaSubgroupIn K)
  (ha : a ∈ A) :
-- imply
  σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by
-- proof
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ

  have hmem : ((τ : L ≃ₐ[K] L) a) ∈ A := (A.subMulAction K).smul_mem τ ha
  refine ⟨hmem, ?_⟩

  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) τ = 1 :=
    MonoidHom.mem_ker.mp hτ
  have hsmul : τ • (⟨a, ha⟩ : A) = ⟨(τ : L ≃ₐ[K] L) a, hmem⟩ := rfl
  have hres : IsLocalRing.residue A ⟨(τ : L ≃ₐ[K] L) a, hmem⟩ = IsLocalRing.residue A ⟨a, ha⟩ := by
    rw [← hsmul, IsLocalRing.ResidueField.residue_smul]
    show (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) τ)
        (IsLocalRing.residue A ⟨a, ha⟩) = _
    rw [hker]
    rfl
  have hmem' : (⟨(τ : L ≃ₐ[K] L) a, hmem⟩ - ⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by rw [map_sub, hres, sub_self])
  exact (A.valuation_lt_one_iff _).mp hmem'


-- created on 2026-10-23
