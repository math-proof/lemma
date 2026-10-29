import Lemma.AutomorphicForm.GodementSection
import Lemma.AutomorphicForm.WeylIntertwining
import Def.AutomorphicForm_UnipotentQuotient
import Lemma.AutomorphicForm.WindowedSiegelSet
import Lemma.LanglandsTunnell.TateLocalZeta
import Abbrev.LanglandsTunnell_RS22GlobalIntegral

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel

noncomputable section

namespace LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Global

variable (F : Type) [Field F] [NumberField F]

open scoped NNReal in

def moduleChar : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

theorem val_moduleChar_apply (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((moduleChar F x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := rfl

theorem moduleChar_pos : ∀ x : (AdeleRing (𝓞 F) F)ˣ, 0 < ((moduleChar F x : ℝˣ) : ℝ) :=
  fun x => NumberField.TateGlobal.ideleNorm_pos x

def godementEisenstein {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  godementSection F ν₀ μ ν α hα Φ s g +
    ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)

theorem godementEisenstein_def {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ}
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    godementEisenstein F ν₀ μ ν α hα Φ s g =
      godementSection F ν₀ μ ν α hα Φ s g +
        ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) :=
  rfl

def rs22GlobalIntegral (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  ∫ g in D, φ g * φ' g * Es g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

theorem rs22GlobalIntegral_def (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ) :
    rs22GlobalIntegral F D φ φ' Es = ∫ g in D, φ g * φ' g * Es g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
  rfl

@[simp] theorem rs22GlobalIntegral_zero_left (D : Set (AdelicGL2 (𝓞 F) F))
    (φ' Es : AdelicGL2 (𝓞 F) F → ℂ) : rs22GlobalIntegral F D 0 φ' Es = 0 := by
  simp [rs22GlobalIntegral]

@[simp] theorem rs22GlobalIntegral_zero_right (D : Set (AdelicGL2 (𝓞 F) F))
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) : rs22GlobalIntegral F D φ φ' 0 = 0 := by
  simp [rs22GlobalIntegral]

theorem rs22GlobalIntegral_add_right (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' E₁ E₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (h₁ : IntegrableOn (fun g => φ g * φ' g * E₁ g) D (adelicGLHaar (Fin 2) (𝓞 F) F))
    (h₂ : IntegrableOn (fun g => φ g * φ' g * E₂ g) D (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    rs22GlobalIntegral F D φ φ' (E₁ + E₂) =
      rs22GlobalIntegral F D φ φ' E₁ + rs22GlobalIntegral F D φ φ' E₂ := by
  simp only [rs22GlobalIntegral, Pi.add_apply, mul_add]
  exact integral_add h₁ h₂

theorem rs22GlobalIntegral_smul_right (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ)
    (c : ℂ) : rs22GlobalIntegral F D φ φ' (c • Es) = c * rs22GlobalIntegral F D φ φ' Es := by
  simp only [rs22GlobalIntegral, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext g; ring

def rs22Kernel (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    Φ (bottomRowVec F g 1)

theorem rs22Kernel_def (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    rs22Kernel F μ α hα Φ s g =
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        Φ (bottomRowVec F g 1) :=
  rfl

def rs22WhittakerIntegral (W W' : AdelicGL2 (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) : ℂ :=
  ∫ q : UnipotentQuotient F, W q.out * W' q.out * rs22Kernel F μ α hα Φ s q.out
    ∂(unipotentQuotientMeasure F)

theorem rs22WhittakerIntegral_def (W W' : AdelicGL2 (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) :
    rs22WhittakerIntegral F W W' μ α hα Φ s =
      ∫ q : UnipotentQuotient F, W q.out * W' q.out * rs22Kernel F μ α hα Φ s q.out
        ∂(unipotentQuotientMeasure F) :=
  rfl

def IsRapidlyDecreasingOnSiegelSets (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c → ∀ N : ℕ, ∃ C : ℝ,
    ∀ g ∈ integralWindowedSiegelSet F c u,
      ‖φ (g * t)‖ * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N ≤ C

def IsUniformlySiegelBounded (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
    ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ∀ g ∈ integralWindowedSiegelSet F c u,
        ‖H s (g * t)‖ ≤ A * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N

theorem isRapidlyDecreasingOnSiegelSets_zero : IsRapidlyDecreasingOnSiegelSets F (fun _ => (0 : ℂ)) :=
  fun _ _ _ _ _ => ⟨0, fun _ _ => by simp⟩

theorem isUniformlySiegelBounded_zero : IsUniformlySiegelBounded F (fun _ _ => (0 : ℂ)) :=
  fun _ _ _ _ _ _ => ⟨0, 0, fun _ _ _ _ _ => by simp⟩

theorem IsRapidlyDecreasingOnSiegelSets.bounded {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsRapidlyDecreasingOnSiegelSets F φ) (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) (hc : 0 < c) :
    ∃ C : ℝ, ∀ g ∈ integralWindowedSiegelSet F c u, ‖φ (g * t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := h c u t hc 0
  exact ⟨C, fun g hg => by simpa using hC g hg⟩

end Global

section Local

def rs22LocalIntegral {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (W W' Φrow m : G → ℂ) (δ : G → ℝ) (s : ℂ) : ℂ :=
  ∫ g, W g * W' g * Φrow g * m g * ((δ g : ℝ) : ℂ) ^ (s + 1 / 2) ∂(μG.withDensity (HaarQuotient.density H μH))

variable {F : Type} [Field F] [NumberField F]

def bottomRow {K : Type*} [CommRing K] (g : GL (Fin 2) K) : Fin 2 → K :=
  fun j => (g : Matrix (Fin 2) (Fin 2) K) 1 j

def rs22FinIntegral (v : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (GL (Fin 2) (v.adicCompletion F))]
    (μG : Measure (GL (Fin 2) (v.adicCompletion F))) (μN : Measure (unipotentSubgroup (v.adicCompletion F)))
    (W W' : GL (Fin 2) (v.adicCompletion F) → ℂ) (Φv : (Fin 2 → v.adicCompletion F) → ℂ)
    (μv : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  rs22LocalIntegral μG (unipotentSubgroup (v.adicCompletion F)) μN W W'
    (fun g => Φv (bottomRow g)) (fun g => ((μv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (fun g => (LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ)) s

def rs22PlaceIntegral (w : InfinitePlace F) [MeasurableSpace (GL (Fin 2) w.Completion)]
    (μG : Measure (GL (Fin 2) w.Completion)) (μN : Measure (unipotentSubgroup w.Completion))
    (W W' : GL (Fin 2) w.Completion → ℂ) (Φw : (Fin 2 → w.Completion) → ℂ)
    (μw : (w.Completion)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  rs22LocalIntegral μG (unipotentSubgroup w.Completion) μN W W'
    (fun g => Φw (bottomRow g)) (fun g => ((μw (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (fun g => (LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (w.Completion)ˣ) : w.Completion) : ℝ)) s

open scoped Classical in

def unramifiedTest2 (v : HeightOneSpectrum (𝓞 F)) : (Fin 2 → v.adicCompletion F) → ℂ :=
  fun x => if ∀ j, x j ∈ v.adicCompletionIntegers F then 1 else 0

theorem unramifiedTest2_apply_of_mem (v : HeightOneSpectrum (𝓞 F)) {x : Fin 2 → v.adicCompletion F}
    (hx : ∀ j, x j ∈ v.adicCompletionIntegers F) : unramifiedTest2 v x = 1 := by
  classical
  simp [unramifiedTest2, hx]

theorem unramifiedTest2_apply_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {x : Fin 2 → v.adicCompletion F}
    (hx : ¬ ∀ j, x j ∈ v.adicCompletionIntegers F) : unramifiedTest2 v x = 0 := by
  classical
  simp [unramifiedTest2, hx]

@[simp] theorem rs22LocalIntegral_zero_left {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (W' Φrow m : G → ℂ) (δ : G → ℝ) (s : ℂ) :
    rs22LocalIntegral μG H μH 0 W' Φrow m δ s = 0 := by
  simp [rs22LocalIntegral]

end Local

end LanglandsTunnell.RankinSelberg

end
