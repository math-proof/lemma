import Lemma.TwistedNormClasses.Main
import Def.AutomorphicForm_GL2ConjugacyCells
import Def.AutomorphicForm_TruncationOperator
import Def.NumberField_AdelicHeight
import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm
import Def.AutomorphicForm_BorelSubgroup
import Def.AutomorphicForm_SigmaAdelicAction
import Def.NumberField_AdelicBox
import Instance.NumberField_AdelicHaar
import Def.M4aHerbrand_IdeleClassVocab

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

namespace AutomorphicForm.TwistedBruhat

def normUnipotentSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
    γ ∈ AutomorphicForm.unipotentCell K ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}

def borelNormOneSet (K L : Type) [Field K] [Field L] [Algebra K L] : Set (GL (Fin 2) L) :=
  {γ : GL (Fin 2) L |
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}

def IsCuspTransversal (L : Type) [Field L] (reps : Set (GL (Fin 2) L)) : Prop :=
  ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ AutomorphicForm.borelSubgroup L

noncomputable def cuspKernel (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L β *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g))

noncomputable def cuspTruncation (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
    (AutomorphicForm.centralScalar (𝓞 L) L z * g)

end AutomorphicForm.TwistedBruhat
