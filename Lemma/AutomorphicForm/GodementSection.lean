import Def.NumberField_AdelicFourier
import Lemma.NumberField.TateGlobalZeta
import Lemma.AutomorphicForm.EtaFamily
import Def.AutomorphicForm_GodementSection

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace NumberField.AdelicFourier

variable (F : Type*) [Field F] [NumberField F]


variable {F}


theorem pairChar_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : Fin 2 → AdeleRing (𝓞 F) F) :
    pairChar ψ v = ψ (v 0 + v 1) := rfl


open scoped Classical in
theorem tensor_mem_pureTensorSet2 (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
    (h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
      ∈ pureTensorSet2 F :=
  ⟨g, h, hlc, hcs, rfl⟩

theorem mem_schwartzBruhat2_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) : Φ ∈ schwartzBruhat2 F :=
  Submodule.subset_span hΦ

theorem zero_mem_schwartzBruhat2 : (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) ∈ schwartzBruhat2 F :=
  Submodule.zero_mem _

theorem schwartzBruhat2_induction
    {p : (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) → Φ ∈ schwartzBruhat2 F → Prop}
    (tensor : ∀ (Φ) (hΦ : Φ ∈ pureTensorSet2 F), p Φ (mem_schwartzBruhat2_of_mem_pureTensorSet2 hΦ))
    (zero : p 0 zero_mem_schwartzBruhat2)
    (add : ∀ Φ Ψ (hΦ : Φ ∈ schwartzBruhat2 F) (hΨ : Ψ ∈ schwartzBruhat2 F),
      p Φ hΦ → p Ψ hΨ → p (Φ + Ψ) (Submodule.add_mem _ hΦ hΨ))
    (smul : ∀ (c : ℂ) Φ (hΦ : Φ ∈ schwartzBruhat2 F), p Φ hΦ → p (c • Φ) (Submodule.smul_mem _ c hΦ))
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) : p Φ hΦ :=
  Submodule.span_induction tensor zero add smul hΦ

end NumberField.AdelicFourier

end
