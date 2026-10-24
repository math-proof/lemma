import Lemma.Definitions.Def_AutomorphicForm_BorelSubgroup

noncomputable section

namespace AutomorphicForm

section InducedSection

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInducedSection (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL2 R K → ℂ) : Prop :=
  ∀ (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (g : AdelicGL2 R K),
    φ (b * g)
      = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * φ g

variable {R K}

theorem isInducedSection_zero (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ₁ χ₂ (fun _ => (0 : ℂ)) := by
  intro b hb g
  simp

theorem chiDet_mul (χ : (AdeleRing R K)ˣ →* ℂˣ) (x y : AdelicGL2 R K) :
    chiDet R K χ (x * y) = chiDet R K χ x * chiDet R K χ y := by
  unfold chiDet
  rw [map_mul, map_mul, Units.val_mul]

theorem isInducedSection_chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ χ (chiDet R K χ) := by
  intro b hb g
  rw [chiDet_mul]
  congr 1
  show chiDet R K χ b = _
  unfold chiDet
  rw [det_borel_eq_diag_mul hb, map_mul, Units.val_mul]

def inducedSectionSubmodule (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) where
  carrier := {φ | IsInducedSection R K χ₁ χ₂ φ}
  zero_mem' := isInducedSection_zero χ₁ χ₂
  add_mem' := by
    intro φ ψ hφ hψ b hb g
    show φ (b * g) + ψ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (φ g + ψ g)
    rw [hφ b hb g, hψ b hb g]
    ring
  smul_mem' := by
    intro c φ hφ b hb g
    show c * φ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (c * φ g)
    rw [hφ b hb g]
    ring

@[simp] theorem mem_inducedSectionSubmodule_iff (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ)
    {φ : AdelicGL2 R K → ℂ} :
    φ ∈ inducedSectionSubmodule χ₁ χ₂ ↔ IsInducedSection R K χ₁ χ₂ φ := Iff.rfl

theorem IsInducedSection.rightTranslate {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (h : AdelicGL2 R K) :
    IsInducedSection R K χ₁ χ₂ (fun g => φ (g * h)) := by
  intro b hb g
  show φ (b * g * h) = _
  rw [mul_assoc, hφ b hb (g * h)]

theorem rightTranslate_mem_inducedSectionSubmodule {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : φ ∈ inducedSectionSubmodule χ₁ χ₂) (h : AdelicGL2 R K) :
    (fun g => φ (g * h)) ∈ inducedSectionSubmodule χ₁ χ₂ :=
  IsInducedSection.rightTranslate hφ h

theorem isInducedSection_unipotent_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (x : AdeleRing R K)
    (g : AdelicGL2 R K) :
    φ (unipotentGL2 x * g) = φ g := by
  rw [hφ (unipotentGL2 x) (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2]
  simp

theorem isInducedSection_centralScalar_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL2 R K) :
    φ (centralScalar R K z * g) = ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ (centralScalar R K z) (centralScalar_mem_adelicBorel R K z) g,
    borelDiagFst_centralScalar R K z (centralScalar_mem_adelicBorel R K z),
    borelDiagSnd_centralScalar R K z (centralScalar_mem_adelicBorel R K z)]
end InducedSection

end AutomorphicForm
