import Lemma.AutomorphicForm.ProductionPinsGeneral
import Lemma.AutomorphicForm.WhittakerCoefficient
import Lemma.NumberField.AdelicTraceFin
import Def.AutomorphicForm_BoundedGenuineCuspRealization

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm.WindowedSiegel

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


variable {F}

theorem boundedGenuineCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (boundedGenuineCuspNotionOf pins).IsCusp F Φ ↔
      IsArithBoundedGenuineCuspRealizable F (pins F) (NumberField.StandardAddChar.stdAddChar F) Φ :=
  Iff.rfl

theorem isBoundedGenuineFn_iff (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F pins ψ φ ↔
      Continuous φ ∧
        (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
          ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C) ∧
        (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  Iff.rfl

theorem isBoundedGenuineCuspRealizable_iff (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) :
    IsBoundedGenuineCuspRealizable F pins ψ Φ ↔
      ∃ R : SmoothCuspRealizationAt F pins Φ,
        Continuous R.toFun ∧
          (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
            ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
              ‖R.toFun g‖ ≤ C) ∧
          (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ R.toFun α g) ∧
          ∀ g : AdelicGL2 (𝓞 F) F,
            Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  Iff.rfl

theorem isBoundedGenuineFn_productionPinsOf_iff
    (D D' : Set (AdelicGL2 (𝓞 F) F))
    (U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F (productionPinsOf F D U gen B) ψ φ ↔
      IsBoundedGenuineFn F (productionPinsOf F D' U' gen' B) ψ φ :=
  Iff.rfl

namespace IsBoundedGenuineFn

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}

theorem continuous (h : IsBoundedGenuineFn F pins ψ φ) : Continuous φ :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineFn F pins ψ φ) :
    IsBoundedOnSiegelWindows F φ :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineFn F pins ψ φ) (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineFn F pins ψ φ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ φ α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineFn F pins ψ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  h.2.2.2 g

end IsBoundedGenuineFn

private theorem det_unipotentGL2 {A : Type*} [CommRing A] (x : A) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

theorem whittakerCoefficient_detTwist (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g
      = c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, map_mul, det_unipotentGL2, one_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem IsBoundedGenuineFn.detTwist {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsBoundedGenuineFn F pins ψ φ)
    (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1) :
    IsBoundedGenuineFn F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) := by
  obtain ⟨hφ, hb, hint, hsum⟩ := h
  refine ⟨hc.mul hφ, fun c' u d₁ d₂ T hc' hd₁ => ?_, fun α g => ?_, fun g => ?_⟩
  · obtain ⟨C, hC⟩ := hb c' u d₁ d₂ T hc' hd₁
    refine ⟨C, fun g hg => ?_⟩
    calc ‖c (Matrix.GeneralLinearGroup.det g) * φ g‖
          = ‖c (Matrix.GeneralLinearGroup.det g)‖ * ‖φ g‖ := norm_mul _ _
      _ ≤ ‖φ g‖ := mul_le_of_le_one_left (norm_nonneg _) (hc₁ _)
      _ ≤ C := hC g hg
  · have hi := hint α g
    letI := pins.nS
    change MeasureTheory.Integrable _ _ at hi ⊢
    simp only [map_mul, det_unipotentGL2, one_mul, mul_assoc]
    exact hi.const_mul _
  · have key : (fun α : F => whittakerCoefficient F pins ψ
        (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g)
        = fun α : F => c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g :=
      funext fun α => whittakerCoefficient_detTwist pins ψ c φ α g
    rw [key]
    exact (hsum g).mul_left _

namespace IsBoundedGenuineCuspRealizationAt

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
  {R : SmoothCuspRealizationAt F pins Φ}

theorem isBoundedGenuineFn (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedGenuineFn F pins ψ R.toFun :=
  h

theorem isGenuineCuspRealizationAt (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsGenuineCuspRealizationAt F pins Φ R :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedOnSiegelWindows F R.toFun :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖R.toFun g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ R.toFun α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  h.2.2.2 g

theorem of_toFun_eq {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact h

theorem detTwist {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1)
    (he : R'.toFun = fun g => c (Matrix.GeneralLinearGroup.det g) * R.toFun g) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact IsBoundedGenuineFn.detTwist h c hc hc₁

end IsBoundedGenuineCuspRealizationAt

theorem isBoundedGenuineCuspRealizationAt_of_isBoundedGenuineFn {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Φ) (h : IsBoundedGenuineFn F pins ψ R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ R :=
  h

theorem IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf
    {D D' : Set (AdelicGL2 (𝓞 F) F)} {U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
    {B : Set (AdeleRing (𝓞 F) F)} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {Φ Φ' : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ}
    {R' : SmoothCuspRealizationAt F (productionPinsOf F D' U' gen' B) Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D U gen B) ψ Φ R)
    (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D' U' gen' B) ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact (isBoundedGenuineFn_productionPinsOf_iff D D' U U' gen gen' B ψ R.toFun).mp h

theorem IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsBoundedGenuineCuspRealizable F pins ψ Φ) : IsGenuineCuspRealizable F pins Φ :=
  h.imp fun _ hR => hR.isGenuineCuspRealizationAt

theorem IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsArithBoundedGenuineCuspRealizable F pins ψ Φ) :
    IsArithGenuineCuspRealizable F pins Φ :=
  IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable h

theorem IsArithBoundedGenuineCuspRealizableVia.isArithGenuineCuspRealizableVia
    {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {R : Type*} [CommRing R]
    {ι : R →+* ℂ} {Φ : HeckeEigensystem F R}
    (h : IsArithBoundedGenuineCuspRealizableVia F pins ψ ι Φ) :
    IsArithGenuineCuspRealizableVia F pins ι Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

theorem boundedGenuineCuspNotionOf_isCusp_imp
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (h : (boundedGenuineCuspNotionOf pins).IsCusp F Φ) :
    (genuineCuspNotionOf pins).IsCusp F Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

end AutomorphicForm

end
