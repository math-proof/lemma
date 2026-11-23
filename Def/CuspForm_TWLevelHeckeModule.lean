import Mathlib
import Abbrev.CuspForm_AuxLevelHeckeModule
import Inductive.CuspForm_TWLevelHeckeModule_Gen
import Abbrev.CuspForm_TWLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.TWLevel

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ)

def level : ℕ := N * (∏ i, qv i) * r

def piQ (p : ℕ) (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    (ZMod (level N r qv))ˣ →* Delta qv p :=
  MonoidHom.pi fun i => (πΔ i).comp (ZMod.unitsMap (dvd_level_q N r qv i))

def HR : Subgroup (ZMod (level N r qv))ˣ := (ZMod.unitsMap (dvd_level_r N r qv)).ker

def HQ (p : ℕ) (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    Subgroup (ZMod (level N r qv))ˣ :=
  HR N r qv ⊓ (piQ N r qv p πΔ).ker

end Level

section Ops

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ)

abbrev Carrier : Type := CohCarrier.H1 (level N r qv) H 𝒪

def op [∀ i, NeZero (qv i)] : Gen (level N r qv) S t → Module.End 𝒪 (Carrier N r qv 𝒪 H)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (level N r qv) H 𝒪 ℓ
  | .U i => CohCarrier.heckeTL (level N r qv) H 𝒪 (qv i)

def OpComm [∀ i, NeZero (qv i)] : Prop :=
  ∀ g h : Gen (level N r qv) S t,
    op N r qv S 𝒪 H g * op N r qv S 𝒪 H h = op N r qv S 𝒪 H h * op N r qv S 𝒪 H g

def thetaQ [NeZero N] (k : Type) [NonAssocSemiring k] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* k)
    (α : Fin t → k) : Gen (level N r qv) S t → k
  | .T _ hℓ hℓS hℓL => θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS)
  | .U i => α i

def heckeData [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H) :
    MvPolynomial.HeckeData 𝒪 (Carrier N r qv 𝒪 H) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen (level N r qv) S t
  op := op N r qv S 𝒪 H
  comm := hc
  θbar := thetaQ N r qv S (IsLocalRing.ResidueField 𝒪) θ α

abbrev ML [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H) : Type :=
  (heckeData N r qv S 𝒪 H θ α hc).ML

def DiaComm [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] : Prop :=
  ∀ (u : (ZMod (level N r qv))ˣ) (g : Gen (level N r qv) S t),
    CohCarrier.diamondL (level N r qv) H 𝒪 u * op N r qv S 𝒪 H g =
      op N r qv S 𝒪 H g * CohCarrier.diamondL (level N r qv) H 𝒪 u

variable [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H)

def diamondLin (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ) :
    Carrier N r qv 𝒪 H →ₗ[(heckeData N r qv S 𝒪 H θ α hc).FreeAlg] Carrier N r qv 𝒪 H where
  toFun := CohCarrier.diamondL (level N r qv) H 𝒪 u
  map_add' := map_add _
  map_smul' f v := by
    show CohCarrier.diamondL (level N r qv) H 𝒪 u ((heckeData N r qv S 𝒪 H θ α hc).opAlgHom f v) =
      (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f (CohCarrier.diamondL (level N r qv) H 𝒪 u v)
    exact congrArg (fun T : Module.End 𝒪 (Carrier N r qv 𝒪 H) => T v)
      (diamondL_opAlgHom_comm N r qv S 𝒪 H θ α hc hdc u f)

def diaML (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ) :
    ML N r qv S 𝒪 H θ α hc →ₗ[𝒪] ML N r qv S 𝒪 H θ α hc :=
  ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl
      (diamondLin N r qv S 𝒪 H θ α hc hdc u)).restrictScalars
        (heckeData N r qv S 𝒪 H θ α hc).FreeAlg).restrictScalars 𝒪

end Ops

end CuspForm.TWLevel

end
