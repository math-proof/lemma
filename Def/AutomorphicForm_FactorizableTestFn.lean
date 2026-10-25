import Lemma.NumberField.AdelicLevel
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.LocallyConstant.Basic

open NumberField IsDedekindDomain

noncomputable section

open scoped Classical

namespace AutomorphicForm

variable (F : Type) [Field F]

def archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)


variable [NumberField F]

def IsArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  (∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, fa g = Φ (archEntries F g)) ∧
    HasCompactSupport fa


def IsFinTestFactor (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  IsLocallyConstant ff ∧ HasCompactSupport ff

def IsFactorizableTestFn (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
    IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧
      ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)

end AutomorphicForm

end
