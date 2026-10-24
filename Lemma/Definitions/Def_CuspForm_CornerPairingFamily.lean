import Lemma.Definitions.Def_CohCarrier_Inst
import Lemma.Definitions.Def_ModularCurve_PeriodMap
import Lemma.Definitions.Def_CohCarrier_LevelPairing

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

namespace CuspForm

open CohCarrier IharaLemma IharaTower

namespace Bfam

variable (𝒪 : Type) [CommRing 𝒪]

def LevelBlock
    (B : (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪) :
    Prop :=
  ∀ (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1),
    IsUnit ((H.index : ℕ) : 𝒪) →
    Function.Bijective (B M H h₁) ∧
    (∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
      ∀ (x y Tx Ty : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
          (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        (Tx : H1 M H 𝒪) = heckeT M H ℓ 𝒪 x → (Ty : H1 M H 𝒪) = heckeT M H ℓ 𝒪 y →
        B M H h₁ Tx y = B M H h₁ x Ty) ∧
    (∀ (d : (ZMod M)ˣ) (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
          (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        diamondL M H 𝒪 d (x : H1 M H 𝒪) = x)

def DegeneracyBlock
    (B : (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪) :
    Prop :=
  ∀ (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
      (h₁ : LevelLE M M ⊤ H 1) (h₁' : LevelLE M' M' ⊤ H' 1)
      (d d' : ℕ) [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
      (hdd' : d * d' = M' / M)
      (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H),
      IsUnit ((H.index : ℕ) : 𝒪) → IsUnit ((H'.index : ℕ) : 𝒪) →
      ∀ (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)))
        (y : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
        (ix : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
        (jy : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
      (ix : H1 M' H' 𝒪) = iDegL M M' H H' d 𝒪 𝒪 h x →
      (jy : H1 M H 𝒪) = jDegL M M' H H' d' 𝒪 𝒪 h' y →
      B M H h₁ jy x = B M' H' h₁' y ix

end Bfam

def Bfam (𝒪 : Type) [CommRing 𝒪] :
    (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪 :=
  Classical.epsilon fun B => Bfam.LevelBlock 𝒪 B ∧ Bfam.DegeneracyBlock 𝒪 B

namespace Bfam

section Corner

variable (𝒪 : Type) [CommRing 𝒪] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1)
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M H 𝒪)]

def cornerInclusion (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.cornerModule →ₗ[𝒪]
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) where
  toFun x := ⟨x, hW _ x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cornerInclusion_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x : cd.cornerModule) :
    cornerInclusion 𝒪 M H h₁ cd hW x = ⟨x, hW _ x.2⟩ := rfl

def cornerRestrict (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.cornerModule →ₗ[𝒪] cd.cornerModule →ₗ[𝒪] 𝒪 :=
  (Bfam 𝒪 M H h₁).compl₁₂ (cornerInclusion 𝒪 M H h₁ cd hW) (cornerInclusion 𝒪 M H h₁ cd hW)

@[simp] theorem cornerRestrict_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x y : cd.cornerModule) :
    cornerRestrict 𝒪 M H h₁ cd hW x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := rfl

theorem pairing_eq_cornerRestrict_iff (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.pairing.B = cornerRestrict 𝒪 M H h₁ cd hW ↔
      ∀ x y : cd.cornerModule, cd.pairing.B x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := by
  constructor
  · intro h x y
    rw [h]
    rfl
  · intro h
    exact LinearMap.ext₂ fun x y => h x y

end Corner

end Bfam

namespace Bfam₀

variable (𝒪 : Type) [CommRing 𝒪]

def Block
    (B : (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪) : Prop :=
  (∀ (M : ℕ) [NeZero M],
    Function.Bijective (B M) ∧
    (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
        (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y → B M Tx y = B M x Ty) ∧
    (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
        (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y → B M Dx y = B M x Dy)) ∧
  (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
      (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
      (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
      (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
      (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
      (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
      (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
      (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
      B M jy x = B M' y ix)

end Bfam₀

def Bfam₀ (𝒪 : Type) [CommRing 𝒪] :
    (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪 :=
  Classical.epsilon (Bfam₀.Block 𝒪)

end CuspForm

end
