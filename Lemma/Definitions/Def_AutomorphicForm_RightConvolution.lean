import Lemma.Definitions.Def_NumberField_AdelicHaar

open NumberField

namespace AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def rightConv (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g =>
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
     ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))

theorem rightConv_apply (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f g =
      (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
       ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) :=
  rfl

theorem rightConv_zero_right (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K φ (fun _ => 0) = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_zero_left (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K (fun _ => 0) f = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_comp_mul_left (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (h g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K (fun x => φ (h * x)) f g = rightConv K φ f (h * g) := by
  simp only [rightConv, mul_assoc]

end AutomorphicForm
