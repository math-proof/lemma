import Lemma.Definitions.Def_CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

def baseOp (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (g : Gen N r S) :
    Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪) :=
  haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
  CohCarrier.heckeTL N ⊤ 𝒪 g.ℓ

def BaseOpComm (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] : Prop :=
  ∀ g h : Gen N r S, baseOp N r S 𝒪 g * baseOp N r S 𝒪 h = baseOp N r S 𝒪 h * baseOp N r S 𝒪 g

def baseHeckeData (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    CohCarrier.HeckeData 𝒪 (CohCarrier.H1 N ⊤ 𝒪) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen N r S
  op := baseOp N r S 𝒪
  comm := hc₀
  θbar g := θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)

instance instModuleFreeAlgBaseCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc₀ : BaseOpComm N r S 𝒪) :
    Module (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (CohCarrier.H1 N ⊤ 𝒪) :=
  (baseHeckeData N r S 𝒪 θ hc₀).moduleFreeAlg

abbrev baseML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Type :=
  (baseHeckeData N r S 𝒪 θ hc₀).ML

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg = (heckeData N r S 𝒪 θ hc).FreeAlg := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (baseHeckeData N r S 𝒪 θ hc₀).mTheta = (heckeData N r S 𝒪 θ hc).mTheta := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Module 𝒪 (baseML N r S 𝒪 θ hc₀) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Module (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (baseML N r S 𝒪 θ hc₀) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    IsScalarTower 𝒪 (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (baseML N r S 𝒪 θ hc₀) := by infer_instance

end CuspForm.AuxLevel

end
