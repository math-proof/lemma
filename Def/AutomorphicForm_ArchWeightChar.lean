module

public import Theorem.Matrix.ArchType

@[expose] public section

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section DetOneSubgroup

variable (K : Type*) [NormedField K]

def rowIsometrySubgroup₀ : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det).ker ⊓ rowIsometrySubgroup K

end DetOneSubgroup

section WeightChar

def firstRowℂ (k : GL (Fin 2) ℝ) : ℂ :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩

noncomputable def archWeightOneℝ : rowIsometrySubgroup₀ ℝ →* ℂˣ where
  toFun k := Units.mk0 (firstRowℂ (k : GL (Fin 2) ℝ))
    (firstRowℂ_ne_zero_of_mem k.2)
  map_one' := Units.ext <| Complex.ext (by simp [firstRowℂ]) (by simp [firstRowℂ])
  map_mul' k k' := by
    ext
    exact firstRowℂ_mul_of_mem k'.2

noncomputable def archWeightCharℝ (n : ℤ) : rowIsometrySubgroup₀ ℝ →* ℂˣ :=
  (zpowGroupHom n).comp archWeightOneℝ

end WeightChar

section PredicateZero

variable (F : Type) [Field F] [NumberField F]

def HasArchCharacterAt₀ (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType₀ (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt₀ F w (χ w) φ

end PredicateZero

section Ed9Witness

end Ed9Witness

end AutomorphicForm
