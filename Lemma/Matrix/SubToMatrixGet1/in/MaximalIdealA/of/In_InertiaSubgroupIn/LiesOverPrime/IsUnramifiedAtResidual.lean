import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Adic
import Def.GaloisRep_LocalConditions
import Lemma.Int.P2MUtil

open IsLocalRing

/--
[GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
  {q : ℕ}
  {b : Module.Basis (Fin 2) A ρ.V}
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {i j : Fin 2}
-- given
  (hunr : ρ.residual.IsUnramifiedAt q)
  (hP : P.LiesOverPrime q)
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
-- imply
  LinearMap.toMatrix b b (ρ.ρ σ) i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A := by
-- proof
  have h1 : (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1 := hunr P hP σ hσ

  have h2 := LinearMap.toMatrix_baseChange (IsLocalRing.ResidueField A) (ρ.ρ σ) b b
  rw [h1, LinearMap.toMatrix_one] at h2
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, IsLocalRing.ResidueField.algebraMap_eq] at h3

  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← h3]
  have h4 : IsLocalRing.residue A ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField A)) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h4, sub_self]


-- created on 2026-10-23
