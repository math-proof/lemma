import Lemma.Definitions.Def_NumberField_AdelicLevel
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

theorem archEntries_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    archEntries F g i j = InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) :=
  rfl

variable [NumberField F]

def IsArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  (∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, fa g = Φ (archEntries F g)) ∧
    HasCompactSupport fa

theorem isArchTestFactor_zero : IsArchTestFactor F (fun _ => 0) :=
  ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩

def IsFinTestFactor (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  IsLocallyConstant ff ∧ HasCompactSupport ff

def IsFactorizableTestFn (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
    IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧
      ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)

theorem isFinTestFactor_zero : IsFinTestFactor F (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isFactorizableTestFn_zero : IsFactorizableTestFn F (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => 0, isArchTestFactor_zero F, isFinTestFactor_zero F,
    fun _ => (mul_zero _).symm⟩

theorem IsFactorizableTestFn.eq_zero_of_glArch {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : fa (AdelicLevel.glArch (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, zero_mul]

theorem IsFactorizableTestFn.eq_zero_of_glFin {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : ff (AdelicLevel.glFin (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, mul_zero]

end AutomorphicForm

end
