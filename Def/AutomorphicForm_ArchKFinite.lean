import Lemma.AutomorphicForm.ArchType

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section Generic

variable {G : Type*} [Group G]

def RightTranslatesSpanFinite (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ),
    ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

def archRowIsometrySubgroup (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup w.Completion).map (adelicArchGLInclAt F w)

def IsArchKFiniteAt (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  RightTranslatesSpanFinite (archRowIsometrySubgroup F w) φ

def IsArchKFinite (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, IsArchKFiniteAt F w φ

end Arch

end AutomorphicForm

end
