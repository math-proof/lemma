import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil

open IsLocalRing

/--
[GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsLocalRing R]
  {ρ : GaloisRepAdic R}
  {J : Ideal R}
-- given
  (hJ : ∃ m : ℕ, maximalIdeal R ^ m ≤ J) :
-- imply
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        ρ.trace (σ * τ) - ρ.trace σ ∈ J := by
-- proof
  classical
  obtain ⟨m, hm⟩ := hJ
  obtain ⟨F, hF, hcont⟩ := ρ.isAdicContinuous m
  refine ⟨F, hF, fun σ τ hτ => ?_⟩
  let b := Module.Free.chooseBasis R ρ.V

  have hcoord : ∀ v ∈ (J • (⊤ : Submodule R ρ.V)), ∀ i, b.repr v i ∈ J := by
    intro v hv i
    refine Submodule.smul_induction_on (p := fun v => b.repr v i ∈ J) hv ?_ ?_
    · intro r hr w _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add, Finsupp.add_apply]
      exact J.add_mem hx hy
  have hτv : ∀ v, ρ.ρ τ v - v ∈ J • (⊤ : Submodule R ρ.V) := fun v =>
    Submodule.smul_mono_left hm (hcont τ hτ v)
  have hstab : ∀ v ∈ J • (⊤ : Submodule R ρ.V), ρ.ρ σ v ∈ J • (⊤ : Submodule R ρ.V) := by
    intro v hv
    have : Submodule.map (ρ.ρ σ) (J • ⊤) ≤ J • (⊤ : Submodule R ρ.V) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨v, hv, rfl⟩
  have key : ρ.trace (σ * τ) - ρ.trace σ = LinearMap.trace R ρ.V (ρ.ρ σ * (ρ.ρ τ - 1)) := by
    simp only [GaloisRepAdic.trace, map_mul, mul_sub, mul_one, map_sub]
  rw [key, LinearMap.trace_eq_matrix_trace R b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine J.sum_mem fun i _ => hcoord _ ?_ i
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact hstab _ (hτv (b i))


-- created on 2026-10-23
