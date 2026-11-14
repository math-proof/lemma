import Mathlib
import Lemma.PadicAlgCl.CompletionBridge
set_option autoImplicit false


noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- This is `Gal p` from `Abbrev.PadicComplex_GaloisAction`, written explicitly so this
module does not import that abbrev file (its `galAlgHom` needs `MulSemiringAction`,
which is carved into `Instance.PadicComplex_GaloisAction` and depends on lemmas below). -/
theorem isometry_algEquiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

private instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩

theorem smul_coe (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

private instance mulSemiringAction :
    MulSemiringAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }

theorem continuous_smul_left (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

theorem uniformContinuous_smul_left (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

theorem norm_smul_eq (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

@[simp]
theorem nnnorm_smul_eq (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

theorem isometry_smul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm
    (MulSemiringAction.toRingHom (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] σ)
    (norm_smul_eq p σ)

private instance smulCommClass_gal_padic :
    SMulCommClass (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℚ_[p] ℂ_[p] :=
  inferInstance

private instance smulCommClass_padic_gal :
    SMulCommClass ℚ_[p] (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] :=
  SMulCommClass.symm _ _ _

theorem smul_algebraMap (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

@[simp]
theorem galAlgHom_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ x = σ • x := rfl

theorem smul_coe_padicEmbedding (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (a : AlgebraicClosure ℚ) :
    σ • ((padicEmbedding p a : PadicAlgCl p) : ℂ_[p]) =
      ((padicEmbedding p (localGaloisToGlobal p σ a) : PadicAlgCl p) : ℂ_[p]) := by
  rw [smul_coe, padicEmbedding_localGaloisToGlobal]

end PadicComplex

end


-- created on 2026-10-24
-- updated on 2026-11-14
