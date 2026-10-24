import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Lemma.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Lemma.Definitions.Def_NumberField_TateGlobalZeta

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.CubicInduction

universe u v w

section LocalWhittaker

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]

def IsGL3PsiWhittakerFn (ψ : AddChar F R) (W : GL (Fin 3) F → R) : Prop :=
  ∀ (x y z : F) (g : GL (Fin 3) F), W (upperUnipotent3 x y z * g) = ψ (x + y) * W g

def gl3PsiWhittakerFnSpace (F : Type u) [CommRing F] (R : Type v) [CommRing R]
    (ψ : AddChar F R) : Submodule R (GL (Fin 3) F → R) where
  carrier := {W | IsGL3PsiWhittakerFn ψ W}
  add_mem' := by
    intro W₁ W₂ h₁ h₂ x y z g
    simp only [Pi.add_apply, h₁ x y z g, h₂ x y z g]
    ring
  zero_mem' := by
    intro x y z g
    simp only [Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c W hW x y z g
    simp only [Pi.smul_apply, hW x y z g, smul_eq_mul]
    ring

theorem mem_gl3PsiWhittakerFnSpace_iff (ψ : AddChar F R) (W : GL (Fin 3) F → R) :
    W ∈ gl3PsiWhittakerFnSpace F R ψ ↔ IsGL3PsiWhittakerFn ψ W := Iff.rfl

def gl3AmbientRightTranslate (g : GL (Fin 3) F) : Module.End R (GL (Fin 3) F → R) where
  toFun W := fun h => W (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem gl3AmbientRightTranslate_apply (g : GL (Fin 3) F) (W : GL (Fin 3) F → R)
    (h : GL (Fin 3) F) : gl3AmbientRightTranslate (R := R) g W h = W (h * g) := rfl

theorem rightTranslate_mem_gl3PsiWhittakerFnSpace (ψ : AddChar F R) (g : GL (Fin 3) F)
    {W : GL (Fin 3) F → R} (hW : W ∈ gl3PsiWhittakerFnSpace F R ψ) :
    gl3AmbientRightTranslate g W ∈ gl3PsiWhittakerFnSpace F R ψ := by
  refine (mem_gl3PsiWhittakerFnSpace_iff ψ _).mpr ?_
  intro x y z h
  show W (upperUnipotent3 x y z * h * g) = ψ (x + y) * W (h * g)
  rw [mul_assoc]
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W).mp hW x y z (h * g)

variable {V : Type w} [AddCommGroup V] [Module R V]

def IsGL3WhittakerFunctional (π : GL (Fin 3) F →* Module.End R V) (ψ : AddChar F R)
    (L : V →ₗ[R] R) : Prop :=
  ∀ (x y z : F) (v : V), L (π (upperUnipotent3 x y z) v) = ψ (x + y) * L v

def gl3WhittakerFunctionalSpace (π : GL (Fin 3) F →* Module.End R V) (ψ : AddChar F R) :
    Submodule R (V →ₗ[R] R) where
  carrier := {L | IsGL3WhittakerFunctional π ψ L}
  add_mem' := by
    intro L₁ L₂ h₁ h₂ x y z v
    simp only [LinearMap.add_apply, h₁ x y z v, h₂ x y z v]
    ring
  zero_mem' := by
    intro x y z v
    simp only [LinearMap.zero_apply, mul_zero]
  smul_mem' := by
    intro c L hL x y z v
    simp only [LinearMap.smul_apply, hL x y z v, smul_eq_mul]
    ring

def GL3WhittakerUniquenessStatement (π : GL (Fin 3) F →* Module.End R V) (ψ : AddChar F R) :
    Prop :=
  Module.rank R (gl3WhittakerFunctionalSpace π ψ) ≤ 1

end LocalWhittaker

section Cyclic

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]

def gl3CyclicSubspace (W : GL (Fin 3) F → R) : Submodule R (GL (Fin 3) F → R) :=
  Submodule.span R (Set.range fun h : GL (Fin 3) F => gl3AmbientRightTranslate (R := R) h W)

theorem gl3AmbientRightTranslate_mem_gl3CyclicSubspace (W : GL (Fin 3) F → R) (g : GL (Fin 3) F)
    {f : GL (Fin 3) F → R} (hf : f ∈ gl3CyclicSubspace W) :
    gl3AmbientRightTranslate (R := R) g f ∈ gl3CyclicSubspace W := by
  refine Submodule.span_induction (p := fun f _ => gl3AmbientRightTranslate (R := R) g f ∈
      gl3CyclicSubspace W) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨h, rfl⟩
    refine Submodule.subset_span ⟨g * h, ?_⟩
    funext x
    simp only [gl3AmbientRightTranslate_apply, mul_assoc]
  · simp only [map_zero, Submodule.zero_mem]
  · intro f₁ f₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c f _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

def gl3CyclicRep (W : GL (Fin 3) F → R) : GL (Fin 3) F →* Module.End R (gl3CyclicSubspace W) where
  toFun g := (gl3AmbientRightTranslate (R := R) g).restrict
    (fun _ hf => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → R) (h * 1) = (f : GL (Fin 3) F → R) h
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → R) (h * (g₁ * g₂)) = (f : GL (Fin 3) F → R) (h * g₁ * g₂)
    rw [mul_assoc]

def HasWhittakerMultOne (ψ : AddChar F R) (W : GL (Fin 3) F → R) : Prop :=
  GL3WhittakerUniquenessStatement (gl3CyclicRep W) ψ

theorem gl3CyclicSubspace_zero : gl3CyclicSubspace (0 : GL (Fin 3) F → R) = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact map_zero _

theorem hasWhittakerMultOne_zero [Nontrivial R] (ψ : AddChar F R) :
    HasWhittakerMultOne ψ (0 : GL (Fin 3) F → R) := by
  have hV : ∀ v : gl3CyclicSubspace (0 : GL (Fin 3) F → R), v = 0 := fun v =>
    Subtype.ext ((Submodule.eq_bot_iff _).mp gl3CyclicSubspace_zero _ v.2)
  haveI : Subsingleton (gl3WhittakerFunctionalSpace (gl3CyclicRep (0 : GL (Fin 3) F → R)) ψ) :=
    ⟨fun a b => Subtype.ext (LinearMap.ext fun v => by rw [hV v, map_zero, map_zero])⟩
  unfold HasWhittakerMultOne GL3WhittakerUniquenessStatement
  rw [rank_subsingleton']
  exact zero_le_one

def transposeInv3 (g : GL (Fin 3) F) : GL (Fin 3) F where
  val := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
  inv := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

end Cyclic

section Global

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def whittaker3 (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  letI := pins.nS
  ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂pins.ν ∂pins.ν ∂pins.ν

def IsCuspidalAlongP21 (pins : CarrierPins ℚ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  letI := pins.nS
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP21 ![x, y] * g) ∂pins.ν ∂pins.ν) = 0

def IsCuspidalAlongP12 (pins : CarrierPins ℚ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  letI := pins.nS
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP12 ![x, y] * g) ∂pins.ν ∂pins.ν) = 0

open scoped Classical in

def inducedCoeff (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if TateGlobal.IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0

def psiLoc (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    AddChar (v.adicCompletion ℚ) ℂ :=
  ψ.compAddMonoidHom (NumberField.StandardAddChar.adeleSingleAt ℚ v)

def orth3 : Set (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  {k | (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ * k = 1}

def IsKFinite (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) : Prop :=
  ∃ S : Finset (GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ),
    ∀ k ∈ orth3, (fun x => W (x * k)) ∈ Submodule.span ℂ (S : Set (GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ))

def dualForm (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => Φ (transposeInv3 g)

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

def detNorm (g : AdelicGL2 (𝓞 ℚ) ℚ) : ℝ :=
  NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)

def HasIotaMoments (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
    IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
    ∀ N : ℕ, ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) *
      ENNReal.ofReal (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) < ⊤

def HasWhittakerHalfPlane (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
    IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
    ∫⁻ g in D, (∑' i : MirabolicIndex ℚ,
        (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ENNReal)) *
      ENNReal.ofReal (detNorm g ^ σ) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) < ⊤

def mirabolicTranslate (i : MirabolicIndex ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i))

structure CubicInductionForm (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) where

  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  whittakerArch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ

  centralChar : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ

  dualWhittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g
  central : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (centralChar z : ℂ) * form g
  centralChar_ideleClass : IsIdeleClassChar (𝓞 ℚ) ℚ centralChar
  cuspidalP21 : IsCuspidalAlongP21 pins form
  cuspidalP12 : IsCuspidalAlongP12 pins form
  whittaker_eq : ∀ g, whittaker g = whittaker3 pins ψ form g
  whittaker_law : IsGL3PsiWhittakerFn ψ whittaker
  expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => whittaker (mirabolicTranslate i * g)) (form g)
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (whittakerLoc v)
  factorizable : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
    (∀ v, IsBadPlace K μ v → v ∈ T) →
    (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
    whittaker g = whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
      ∏ v ∈ T, whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v g)
  spherical : ∀ v, ¬ IsBadPlace K μ v →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (whittakerLoc v)
  levelInvariant : ∀ v, ¬ IsRamifiedIn K v →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, whittakerLoc v (g * k) = whittakerLoc v g
  multOne : ∀ v, HasWhittakerMultOne (psiLoc ψ v) (whittakerLoc v)
  moderateGrowth : IsModerateGrowth3 ℚ form
  kFinite : IsKFinite whittakerArch
  iotaMoments : HasIotaMoments form
  whittakerHalfPlane : HasWhittakerHalfPlane whittaker
  dualWhittaker_eq : ∀ g, dualWhittaker g = whittaker3 pins ψ⁻¹ (dualForm form) g
  dualWhittaker_law : IsGL3PsiWhittakerFn ψ⁻¹ dualWhittaker
  dual_expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => dualWhittaker (mirabolicTranslate i * g)) (dualForm form g)
  dual_iotaMoments : HasIotaMoments (dualForm form)
  dual_whittakerHalfPlane : HasWhittakerHalfPlane dualWhittaker

def HasCubicInductionForm (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  ∃ D : CubicInductionForm K pins ψ μ,
    D.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        D.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (D.whittakerLoc v)

theorem not_isCuspidalAlongP21_one (pins : CarrierPins ℚ)
    (h : @IsProbabilityMeasure _ pins.nS pins.ν) :
    ¬ IsCuspidalAlongP21 pins (fun _ => (1 : ℂ)) := by
  letI := pins.nS
  haveI := h
  intro hc
  have h1 := hc 1
  simp at h1

def CubicInductionForm.zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : CubicInductionForm K pins ψ μ where
  form := 0
  whittaker := 0
  whittakerLoc := fun _ _ => 0
  whittakerArch := 0
  centralChar := 1
  dualWhittaker := 0
  automorphic := fun _ _ => rfl
  central := fun _ _ => by simp
  centralChar_ideleClass := fun _ => rfl
  cuspidalP21 := fun _ => by simp
  cuspidalP12 := fun _ => by simp
  whittaker_eq := fun _ => by simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  whittaker_law := fun _ _ _ _ => (mul_zero _).symm
  expansion := fun _ => by simpa only [Pi.zero_apply] using hasSum_zero
  whittakerLoc_law := fun _ _ _ _ _ => (mul_zero _).symm
  factorizable := fun _ _ _ _ => by simp
  spherical := fun v _ => isInducedSphericalAt_zero _ v _
  levelInvariant := fun _ _ _ _ _ => rfl
  multOne := fun v => hasWhittakerMultOne_zero (psiLoc ψ v)
  moderateGrowth := isModerateGrowth3_zero ℚ
  kFinite := ⟨∅, fun _ _ => by
    simp only [Finset.coe_empty, Submodule.span_empty]
    exact Submodule.zero_mem _⟩
  iotaMoments := fun _ _ _ => by
    simp only [Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]
  whittakerHalfPlane := ⟨0, fun _ _ _ _ => by
    simp only [tsum_zero, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]⟩
  dualWhittaker_eq := fun _ => by
    simp only [whittaker3, dualForm, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  dualWhittaker_law := fun _ _ _ _ => (mul_zero _).symm
  dual_expansion := fun _ => by simpa only [dualForm, Pi.zero_apply] using hasSum_zero
  dual_iotaMoments := fun _ _ _ => by
    simp only [dualForm, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]
  dual_whittakerHalfPlane := ⟨0, fun _ _ _ _ => by
    simp only [tsum_zero, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]⟩

end Global

end LanglandsTunnell.CubicInduction

end
