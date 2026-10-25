import Mathlib
import Abbrev.CuspForm_AuxLevelHeckeModule
import Inductive.CuspForm_TWLevelHeckeModule_Gen
import Instance.CuspForm_TWLevelHeckeModule
import Abbrev.CuspForm_TWLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.TWLevel

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ)

def level : ℕ := N * (∏ i, qv i) * r

theorem dvd_level_r : r ∣ level N r qv := dvd_mul_left r _

theorem dvd_level_N : N ∣ level N r qv :=
  (dvd_mul_right N _).trans (dvd_mul_right _ r)

theorem dvd_level_q (i : Fin t) : qv i ∣ level N r qv :=
  ((Finset.dvd_prod_of_mem qv (Finset.mem_univ i)).trans (dvd_mul_left _ N)).trans (dvd_mul_right _ r)

theorem not_dvd_of_not_dvd_level {ℓ : ℕ} (h : ¬ ℓ ∣ level N r qv) : ¬ ℓ ∣ N :=
  fun h' => h (h'.trans (dvd_level_N N r qv))

def piQ (p : ℕ) (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    (ZMod (level N r qv))ˣ →* Delta qv p :=
  MonoidHom.pi fun i => (πΔ i).comp (ZMod.unitsMap (dvd_level_q N r qv i))

@[simp] theorem piQ_apply (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (u : (ZMod (level N r qv))ˣ) (i : Fin t) :
    piQ N r qv p πΔ u i = πΔ i (ZMod.unitsMap (dvd_level_q N r qv i) u) := rfl

def HR : Subgroup (ZMod (level N r qv))ˣ := (ZMod.unitsMap (dvd_level_r N r qv)).ker

def HQ (p : ℕ) (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    Subgroup (ZMod (level N r qv))ˣ :=
  HR N r qv ⊓ (piQ N r qv p πΔ).ker

theorem HQ_le_HR (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    HQ N r qv p πΔ ≤ HR N r qv := inf_le_left

theorem mem_HR_iff (u : (ZMod (level N r qv))ˣ) :
    u ∈ HR N r qv ↔ ZMod.unitsMap (dvd_level_r N r qv) u = 1 := Iff.rfl

theorem mem_HQ_iff (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (u : (ZMod (level N r qv))ˣ) :
    u ∈ HQ N r qv p πΔ ↔ u ∈ HR N r qv ∧ piQ N r qv p πΔ u = 1 := Iff.rfl

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
    CohCarrier.HeckeData 𝒪 (Carrier N r qv 𝒪 H) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen (level N r qv) S t
  op := op N r qv S 𝒪 H
  comm := hc
  θbar := thetaQ N r qv S (IsLocalRing.ResidueField 𝒪) θ α

abbrev ML [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H) : Type :=
  (heckeData N r qv S 𝒪 H θ α hc).ML

theorem X_smul_toML [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H)
    (g : Gen (level N r qv) S t) (v : Carrier N r qv 𝒪 H) :
    (MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) •
        (heckeData N r qv S 𝒪 H θ α hc).toML v =
      (heckeData N r qv S 𝒪 H θ α hc).toML (op N r qv S 𝒪 H g v) := by
  rw [← LinearMap.map_smul]
  congr 1
  show (heckeData N r qv S 𝒪 H θ α hc).opAlgHom (MvPolynomial.X g) v = _
  rw [CohCarrier.HeckeData.opAlgHom_X]
  rfl

def DiaComm [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] : Prop :=
  ∀ (u : (ZMod (level N r qv))ˣ) (g : Gen (level N r qv) S t),
    CohCarrier.diamondL (level N r qv) H 𝒪 u * op N r qv S 𝒪 H g =
      op N r qv S 𝒪 H g * CohCarrier.diamondL (level N r qv) H 𝒪 u

variable [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H)

theorem diamondL_opAlgHom_comm (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    CohCarrier.diamondL (level N r qv) H 𝒪 u * (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f =
      (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f * CohCarrier.diamondL (level N r qv) H 𝒪 u := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show (MvPolynomial.C a : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) =
      algebraMap 𝒪 (heckeData N r qv S 𝒪 H θ α hc).FreeAlg a from rfl, AlgHom.commutes]
    exact (Algebra.commutes a _).symm
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | mul_X p g hp =>
    rw [map_mul, CohCarrier.HeckeData.opAlgHom_X, ← mul_assoc, hp, mul_assoc,
      show (heckeData N r qv S 𝒪 H θ α hc).op g = op N r qv S 𝒪 H g from rfl, hdc u g, ← mul_assoc]

def diamondLin (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ) :
    Carrier N r qv 𝒪 H →ₗ[(heckeData N r qv S 𝒪 H θ α hc).FreeAlg] Carrier N r qv 𝒪 H where
  toFun := CohCarrier.diamondL (level N r qv) H 𝒪 u
  map_add' := map_add _
  map_smul' f v := by
    show CohCarrier.diamondL (level N r qv) H 𝒪 u ((heckeData N r qv S 𝒪 H θ α hc).opAlgHom f v) =
      (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f (CohCarrier.diamondL (level N r qv) H 𝒪 u v)
    exact congrArg (fun T : Module.End 𝒪 (Carrier N r qv 𝒪 H) => T v)
      (diamondL_opAlgHom_comm N r qv S 𝒪 H θ α hc hdc u f)

@[simp] theorem diamondLin_apply (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (v : Carrier N r qv 𝒪 H) :
    diamondLin N r qv S 𝒪 H θ α hc hdc u v = CohCarrier.diamondL (level N r qv) H 𝒪 u v := rfl

def diaML (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ) :
    ML N r qv S 𝒪 H θ α hc →ₗ[𝒪] ML N r qv S 𝒪 H θ α hc :=
  ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl
      (diamondLin N r qv S 𝒪 H θ α hc hdc u)).restrictScalars
        (heckeData N r qv S 𝒪 H θ α hc).FreeAlg).restrictScalars 𝒪

theorem diaML_smul (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) (x : ML N r qv S 𝒪 H θ α hc) :
    diaML N r qv S 𝒪 H θ α hc hdc u (f • x) = f • diaML N r qv S 𝒪 H θ α hc hdc u x :=
  LinearMap.map_smul
    ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl
      (diamondLin N r qv S 𝒪 H θ α hc hdc u)).restrictScalars (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) f x

theorem diaML_toML (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (v : Carrier N r qv 𝒪 H) :
    diaML N r qv S 𝒪 H θ α hc hdc u ((heckeData N r qv S 𝒪 H θ α hc).toML v) =
      (heckeData N r qv S 𝒪 H θ α hc).toML (CohCarrier.diamondL (level N r qv) H 𝒪 u v) := by
  show LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc u) (LocalizedModule.mk v 1) =
    LocalizedModule.mk _ 1
  rw [LocalizedModule.map_mk]
  rfl

end Ops

end CuspForm.TWLevel

end
