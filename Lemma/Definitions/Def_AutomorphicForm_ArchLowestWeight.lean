import Mathlib
import Lemma.Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

noncomputable section

namespace AutomorphicForm

def IsArchLowestWeightAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ σ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

variable {F : Type} [Field F] [NumberField F]

theorem isArchLowestWeightAt_iff (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsArchLowestWeightAt w hw φ ↔
      ∃ σ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
        (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
            (iwasawaSectionGL z))) :=
  Iff.rfl

theorem isArchLowestWeightAt_zero (w : InfinitePlace F) (hw : w.IsReal) :
    IsArchLowestWeightAt w hw (fun _ => 0) :=
  ⟨0, fun _ => by simpa using mdifferentiable_const⟩

theorem IsArchLowestWeightAt.const_mul {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchLowestWeightAt w hw φ) (a : ℂ) :
    IsArchLowestWeightAt w hw (fun g => a * φ g) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun g => ?_⟩
  have := (hσ g).const_smul a
  simpa [Pi.smul_def, smul_eq_mul, mul_left_comm] using this

theorem isArchLowestWeightAt_of_rpow {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (σ : ℝ)
    (h : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) ^ σ : ℝ) : ℂ) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) :
    IsArchLowestWeightAt w hw φ := by
  refine ⟨(σ : ℂ), fun g => ?_⟩
  have hfun : (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ (σ : ℂ)) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) =
      (fun z : UpperHalfPlane =>
      (((z.im : ℝ) ^ σ : ℝ) : ℂ) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) := by
    funext z
    rw [Complex.ofReal_cpow (le_of_lt z.im_pos)]
  rw [hfun]
  exact h g

theorem IsArchHolomorphicAt.isArchLowestWeightAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchHolomorphicAt w hw φ) :
    IsArchLowestWeightAt w hw φ := by
  refine ⟨-1, fun g => ?_⟩
  have hfun : (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ (-1 : ℂ)) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) =
      (fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) := by
    funext z
    rw [Complex.cpow_neg_one]
  rw [hfun]
  exact h g

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @IsArchLowestWeightAt
#print axioms AutomorphicForm.isArchLowestWeightAt_zero
#print axioms AutomorphicForm.IsArchLowestWeightAt.const_mul
#print axioms AutomorphicForm.isArchLowestWeightAt_of_rpow
#print axioms AutomorphicForm.IsArchHolomorphicAt.isArchLowestWeightAt
end Battery
