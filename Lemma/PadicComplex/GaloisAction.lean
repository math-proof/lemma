import Mathlib
import Lemma.GaloisRep.CompletionBridge
import Abbrev.PadicComplex_GaloisAction

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

theorem isometry_algEquiv (σ : Gal p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem smul_coe (σ : Gal p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

theorem continuous_smul_left (σ : Gal p) : Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

theorem uniformContinuous_smul_left (σ : Gal p) : UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

theorem norm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

@[simp]
theorem nnnorm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

theorem isometry_smul (σ : Gal p) : Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm (MulSemiringAction.toRingHom (Gal p) ℂ_[p] σ)
    (norm_smul_eq p σ)


theorem smul_algebraMap (σ : Gal p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

@[simp]
theorem galAlgHom_apply (σ : Gal p) (x : ℂ_[p]) : galAlgHom p σ x = σ • x := rfl

theorem smul_coe_padicEmbedding (σ : Gal p) (a : AlgebraicClosure ℚ) :
    σ • ((padicEmbedding p a : PadicAlgCl p) : ℂ_[p]) =
      ((padicEmbedding p (localGaloisToGlobal p σ a) : PadicAlgCl p) : ℂ_[p]) := by
  rw [smul_coe, padicEmbedding_localGaloisToGlobal]

end PadicComplex

end
