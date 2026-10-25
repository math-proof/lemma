import Lemma.AutomorphicForm.CuspidalConstituent

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsArchSphericalOfType (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x


def IsLevelSphericalOfType (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
    IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
      Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
        (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)

end AutomorphicForm

end
