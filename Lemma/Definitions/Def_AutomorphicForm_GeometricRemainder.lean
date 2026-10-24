import Lemma.Definitions.Def_AutomorphicForm_TruncationOperator
import Lemma.Definitions.Def_AutomorphicForm_AdelicKernel
import Lemma.Definitions.Def_NumberField_AdelicHeight
import Lemma.Definitions.Def_Analysis_HalfLineIntercept
import Lemma.Definitions.Def_AutomorphicForm_CarrierPins
import Lemma.Definitions.Def_NumberField_PrincipalLevel
import Lemma.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Lemma.Definitions.Def_NumberField_AdelicBox

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain

noncomputable section

def AutomorphicForm.geometricRemainder
    (K : Type) [Field K] [NumberField K]
    (ΦK Φ₀K : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φK : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  HalfLine.intercept (fun R : ℝ =>
    (∫ x in Φ₀K, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y => AutomorphicForm.adelicKernel K φK x y)
          (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
    (∫ x in ΦK, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelCentralPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
          AutomorphicForm.adelicKernelEllipticPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

open AutomorphicForm in

example
    (K : Type) [Field K] [NumberField K]
    (ΦK Φ₀K : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    AutomorphicForm.geometricRemainder K ΦK Φ₀K νZK ΩK ξ (fun _ => 0) = 0 := by
  unfold AutomorphicForm.geometricRemainder
  refine HalfLine.intercept_eq_of_forall_le_eq_add_mul (ν := 0) ⟨0, fun R _ => ?_⟩
  simp [AutomorphicForm.adelicKernel, AutomorphicForm.adelicKernelCentralPart,
    AutomorphicForm.adelicKernelEllipticPart, AutomorphicForm.lambdaT_zero]

end
