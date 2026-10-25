import Lemma.CohCarrier.Inst
import Lemma.CuspForm.HeckeAlgebra
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Instance.CuspForm_AuxLevelHeckeModule
import Structure.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel


def subgroup (N r : ℕ) : Subgroup (ZMod (N * r))ˣ :=
  (ZMod.unitsMap (dvd_mul_left r N)).ker

abbrev Carrier (N r : ℕ) (𝒪 : Type) [CommRing 𝒪] : Type :=
  CohCarrier.H1 (N * r) (subgroup N r) 𝒪

def op (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (g : Gen N r S) :
    Module.End 𝒪 (Carrier N r 𝒪) :=
  haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
  CohCarrier.heckeTL (N * r) (subgroup N r) 𝒪 g.ℓ

def OpComm (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] : Prop :=
  ∀ g h : Gen N r S, op N r S 𝒪 g * op N r S 𝒪 h = op N r S 𝒪 h * op N r S 𝒪 g

def heckeData (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc : OpComm N r S 𝒪) :
    CohCarrier.HeckeData 𝒪 (Carrier N r 𝒪) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen N r S
  op := op N r S 𝒪
  comm := hc
  θbar g := θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)

abbrev ML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc : OpComm N r S 𝒪) : Type :=
  (heckeData N r S 𝒪 θ hc).ML

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc : OpComm N r S 𝒪) :
    Module 𝒪 (ML N r S 𝒪 θ hc) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc : OpComm N r S 𝒪) :
    Module (heckeData N r S 𝒪 θ hc).FreeAlg (ML N r S 𝒪 θ hc) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc : OpComm N r S 𝒪) :
    IsScalarTower 𝒪 (heckeData N r S 𝒪 θ hc).FreeAlg (ML N r S 𝒪 θ hc) := by infer_instance

end CuspForm.AuxLevel

end
