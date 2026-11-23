module

public import Mathlib
public import Abbrev.CuspForm_AuxLevelHeckeModule
public import Inductive.CuspForm_TWLevelHeckeModule_Gen
public import Abbrev.CuspForm_TWLevelHeckeModule

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace CuspForm.TWLevel

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ)


public theorem dvd_level_r : r ∣ level N r qv := dvd_mul_left r _


public theorem dvd_level_N : N ∣ level N r qv :=
  (dvd_mul_right N _).trans (dvd_mul_right _ r)


public theorem dvd_level_q (i : Fin t) : qv i ∣ level N r qv :=
  ((Finset.dvd_prod_of_mem qv (Finset.mem_univ i)).trans (dvd_mul_left _ N)).trans (dvd_mul_right _ r)


public theorem not_dvd_of_not_dvd_level {ℓ : ℕ} (h : ¬ ℓ ∣ level N r qv) : ¬ ℓ ∣ N :=
  fun h' => h (h'.trans (dvd_level_N N r qv))


@[simp] public theorem piQ_apply (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (u : (ZMod (level N r qv))ˣ) (i : Fin t) :
    piQ N r qv p πΔ u i = πΔ i (ZMod.unitsMap (dvd_level_q N r qv i) u) := rfl


public theorem HQ_le_HR (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))) :
    HQ N r qv p πΔ ≤ HR N r qv := inf_le_left


public theorem mem_HR_iff (u : (ZMod (level N r qv))ˣ) :
    u ∈ HR N r qv ↔ ZMod.unitsMap (dvd_level_r N r qv) u = 1 := Iff.rfl


public theorem mem_HQ_iff (p : ℕ)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (u : (ZMod (level N r qv))ˣ) :
    u ∈ HQ N r qv p πΔ ↔ u ∈ HR N r qv ∧ piQ N r qv p πΔ u = 1 := Iff.rfl

end Level

section Ops

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ)


public theorem X_smul_toML [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
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


public theorem diamondL_opAlgHom_comm (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
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


@[simp] public theorem diamondLin_apply (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (v : Carrier N r qv 𝒪 H) :
    diamondLin N r qv S 𝒪 H θ α hc hdc u v = CohCarrier.diamondL (level N r qv) H 𝒪 u v := rfl


public theorem diaML_smul (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
    (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) (x : ML N r qv S 𝒪 H θ α hc) :
    diaML N r qv S 𝒪 H θ α hc hdc u (f • x) = f • diaML N r qv S 𝒪 H θ α hc hdc u x :=
  LinearMap.map_smul
    ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl
      (diamondLin N r qv S 𝒪 H θ α hc hdc u)).restrictScalars (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) f x


public theorem diaML_toML (hdc : DiaComm N r qv S 𝒪 H) (u : (ZMod (level N r qv))ˣ)
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
