import Lemma.LanglandsTunnell.CubicInduction_Carrier
import Def.LanglandsTunnell_CubicInduction_HeckeDatum
import Def.LanglandsTunnell_CubicInduction_Growth
import Instance.LanglandsTunnell_CubicInduction_IotaTorus
import Def.LanglandsTunnell_CubicInduction_Congruence
import Def.LanglandsTunnell_CubicInduction_TorusValues
import Structure.AutomorphicForm_WhittakerCoefficient
import Def.NumberField_TateGlobalZeta
import Lemma.AutomorphicForm.SmoothingKernel

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.CubicInduction

export AutomorphicForm (transposeInvN coe_transposeInvN)

universe u v w

section LocalWhittaker

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]

def IsGL3PsiWhittakerFn (ψ : AddChar F R) (W : GL (Fin 3) F → R) : Prop :=
  ∀ (x y z : F) (g : GL (Fin 3) F), W (upperUnipotent3 x y z * g) = ψ (x + y) * W g


def gl3AmbientRightTranslate (g : GL (Fin 3) F) : Module.End R (GL (Fin 3) F → R) where
  toFun W := fun h => W (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem gl3AmbientRightTranslate_apply (g : GL (Fin 3) F) (W : GL (Fin 3) F → R)
    (h : GL (Fin 3) F) : gl3AmbientRightTranslate (R := R) g W h = W (h * g) := rfl


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


end Global

end LanglandsTunnell.CubicInduction

end
