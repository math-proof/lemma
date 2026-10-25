import Mathlib
import Lemma.AutomorphicForm.ViaCompactCuspNotion
import Lemma.AutomorphicForm.ProductionPinsGeneral
import Def.AutomorphicForm_TranslateSpanOccurrence

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


variable {F}

theorem isInTranslateSpanOn_iff (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) :
    IsInTranslateSpanOn F D φ φ' ↔
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
          ∫⁻ y in D, (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε := Iff.rfl

theorem isInTranslateSpanOn_self (D : Set (AdelicGL2 (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsInTranslateSpanOn F D φ φ := by
  intro ε hε
  refine ⟨{1}, fun _ => 1, ?_⟩
  have h0 : (fun y : AdelicGL2 (𝓞 F) F =>
      ((‖φ y - ∑ h ∈ ({1} : Finset (AdelicGL2 (𝓞 F) F)), (1 : ℂ) * φ (y * h)‖₊ : ℝ≥0∞) ^ 2))
        = fun _ => 0 := by
    funext y
    simp
  rw [h0, lintegral_zero]
  exact hε

theorem IsInTranslateSpanOn.of_eq {D : Set (AdelicGL2 (𝓞 F) F)} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (h : φ = φ') : IsInTranslateSpanOn F D φ φ' := by
  subst h; exact isInTranslateSpanOn_self D φ

namespace TranslateSpanOccurrence

theorem agrees_refl (Θ : HeckeEigensystem F ℂ) : Θ.AgreesAwayFromFinite Θ :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩

theorem agrees_symm {Θ Θ' : HeckeEigensystem F ℂ} (h : Θ.AgreesAwayFromFinite Θ') :
    Θ'.AgreesAwayFromFinite Θ := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1.symm, (hS v hv).2.symm⟩⟩

theorem agrees_trans {Θ Θ' Θ'' : HeckeEigensystem F ℂ} (h : Θ.AgreesAwayFromFinite Θ')
    (h' : Θ'.AgreesAwayFromFinite Θ'') : Θ.AgreesAwayFromFinite Θ'' := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨S', hS'⟩ := h'
  refine ⟨S ∪ S', fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hS' v hv.2).1, (hS v hv.1).2.trans (hS' v hv.2).2⟩

end TranslateSpanOccurrence

open TranslateSpanOccurrence

variable (F)


variable {F}

theorem archOccursInClassOf_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral R)
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R.toFun) :
    ArchOccursInClassOf F D Θ P :=
  ⟨Θ, agrees_refl Θ, R, hR, hP⟩

theorem archOccursInClassOf_of_realization_of_agrees {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ Θ' : HeckeEigensystem F ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral R')
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R'.toFun) :
    ArchOccursInClassOf F D Θ P :=
  ⟨Θ', hΘ', R', hR', hP⟩

theorem ArchOccursInClassOf.mono {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ P)
    (hPQ : ∀ φ, P φ → Q φ) : ArchOccursInClassOf F D Θ Q := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hPQ _ hP⟩

theorem ArchOccursInClassOf.and_left {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ (fun φ => P φ ∧ Q φ)) :
    ArchOccursInClassOf F D Θ P :=
  h.mono fun _ hφ => hφ.1

theorem ArchOccursInClassOf.and_right {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ (fun φ => P φ ∧ Q φ)) :
    ArchOccursInClassOf F D Θ Q :=
  h.mono fun _ hφ => hφ.2

theorem ArchOccursInClassOf.of_agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ₁ Θ₂ : HeckeEigensystem F ℂ}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ₁ P)
    (h₁₂ : Θ₁.AgreesAwayFromFinite Θ₂) : ArchOccursInClassOf F D Θ₂ P := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', agrees_trans hΘ' h₁₂, R', hR', hP⟩

theorem archOccursInClassOf_iff_of_agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ₁ Θ₂ : HeckeEigensystem F ℂ}
    (h₁₂ : Θ₁.AgreesAwayFromFinite Θ₂) (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) :
    ArchOccursInClassOf F D Θ₁ P ↔ ArchOccursInClassOf F D Θ₂ P :=
  ⟨fun h => h.of_agrees h₁₂, fun h => h.of_agrees (agrees_symm h₁₂)⟩

theorem ArchOccursInClassOf.exists_continuous {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ' ∧ P φ' := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', hΘ', R'.toFun, hR', hP⟩

theorem ArchOccursInClassOf.isArithGenuineCuspRealizable {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ : HeckeEigensystem F ℂ} {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (h : ArchOccursInClassOf F D Θ P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ' := by
  obtain ⟨Θ', hΘ', R', hR', -⟩ := h
  exact ⟨Θ', hΘ', R', hR'⟩

theorem archOccursInClassOf_true_of_isArithGenuineCuspRealizable {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ Θ' : HeckeEigensystem F ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (h : IsArithGenuineCuspRealizable F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ') :
    ArchOccursInClassOf F D Θ (fun _ => True) := by
  obtain ⟨R', hR'⟩ := h
  exact ⟨Θ', hΘ', R', hR', trivial⟩

variable (F)


variable {F}

theorem archOccursInSpanOf_self {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral R)
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R.toFun) :
    ArchOccursInSpanOf F D Θ R P :=
  ⟨Θ, agrees_refl Θ, R, hR, isInTranslateSpanOn_self D R.toFun, hP⟩

theorem ArchOccursInSpanOf.mono {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P)
    (hPQ : ∀ φ, P φ → Q φ) : ArchOccursInSpanOf F D Θ R Q := by
  obtain ⟨Θ', hΘ', R', hR', hspan, hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hspan, hPQ _ hP⟩

theorem ArchOccursInSpanOf.agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ' ∧ IsInTranslateSpanOn F D R.toFun φ' ∧ P φ' := by
  obtain ⟨Θ', hΘ', R', hR', hspan, hP⟩ := h
  exact ⟨Θ', hΘ', R'.toFun, hR', hspan, hP⟩

theorem ArchOccursInSpanOf.archOccursInClassOf {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P) :
    ArchOccursInClassOf F D Θ P := by
  obtain ⟨Θ', hΘ', R', hR', -, hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hP⟩

end AutomorphicForm

end
