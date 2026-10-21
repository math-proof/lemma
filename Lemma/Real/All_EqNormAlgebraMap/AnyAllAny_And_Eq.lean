import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Padic_exists_complete_algClosed_isometry_algebraicClosure](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Padic_exists_complete_algClosed_isometry_algebraicClosure.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime] :
  -- imply
  ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : IsUltrametricDist K) (_ : CompleteSpace K) (_ : CharZero K) (_ : IsAlgClosed K) (_ : Algebra ℚ_[p] K), (∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖) ∧ ∃ (ι : AlgHom ℚ_[p] (AlgebraicClosure ℚ_[p]) K), ∀ (σ : AlgEquiv ℚ_[p] (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p])), ∃ (σK : RingHom K K), Isometry (⇑σK) ∧ ∀ x, σK (ι x) = ι (σ x) := by
  -- proof
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p], ?_⟩
  ·
    intro x
    rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq, PadicComplex.norm_extends]
    apply PadicAlgCl.norm_extends p x
  ·
    intro σ
    have hσ_norm : ∀ x : PadicAlgCl p, ‖σ x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv σ x).symm
    have hσ_isom : Isometry (σ : PadicAlgCl p → PadicAlgCl p) := AddMonoidHomClass.isometry_of_norm σ hσ_norm
    have hσ_cont : Continuous (⇑(σ : RingHom (PadicAlgCl p) (PadicAlgCl p))) := hσ_isom.continuous
    refine ⟨UniformSpace.Completion.mapRingHom (σ : RingHom (PadicAlgCl p) (PadicAlgCl p)) hσ_cont, ?_, ?_⟩
    ·
      rw [UniformSpace.Completion.coe_mapRingHom]
      apply hσ_isom.completion_map
    ·
      intro x
      have hι : ∀ y, (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]) y = (y : ℂ_[p]) := fun y => (PadicComplex.coe_eq p y).symm
      rw [hι, hι, UniformSpace.Completion.coe_mapRingHom]
      apply UniformSpace.Completion.map_coe hσ_isom.uniformContinuous x


-- created on 2026-10-20
