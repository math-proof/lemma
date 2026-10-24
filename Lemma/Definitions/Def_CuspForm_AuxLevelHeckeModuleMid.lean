import Lemma.Definitions.Def_CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

def midOp (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (g : Gen N r S) :
    Module.End 𝒪 (CohCarrier.H1 (N * r) ⊤ 𝒪) :=
  haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
  CohCarrier.heckeTL (N * r) ⊤ 𝒪 g.ℓ

def MidOpComm (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] : Prop :=
  ∀ g h : Gen N r S, midOp N r S 𝒪 g * midOp N r S 𝒪 h = midOp N r S 𝒪 h * midOp N r S 𝒪 g

def midHeckeData (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    CohCarrier.HeckeData 𝒪 (CohCarrier.H1 (N * r) ⊤ 𝒪) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen N r S
  op := midOp N r S 𝒪
  comm := hc₁
  θbar g := θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)

instance instModuleFreeAlgMidCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc₁ : MidOpComm N r S 𝒪) :
    Module (midHeckeData N r S 𝒪 θ hc₁).FreeAlg (CohCarrier.H1 (N * r) ⊤ 𝒪) :=
  (midHeckeData N r S 𝒪 θ hc₁).moduleFreeAlg

abbrev midML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    Type :=
  (midHeckeData N r S 𝒪 θ hc₁).ML

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (midHeckeData N r S 𝒪 θ hc₁).FreeAlg = (heckeData N r S 𝒪 θ hc).FreeAlg := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (midHeckeData N r S 𝒪 θ hc₁).mTheta = (heckeData N r S 𝒪 θ hc).mTheta := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    Module 𝒪 (midML N r S 𝒪 θ hc₁) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    Module (midHeckeData N r S 𝒪 θ hc₁).FreeAlg (midML N r S 𝒪 θ hc₁) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    IsScalarTower 𝒪 (midHeckeData N r S 𝒪 θ hc₁).FreeAlg (midML N r S 𝒪 θ hc₁) := by infer_instance

end CuspForm.AuxLevel

end
