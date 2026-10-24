import Mathlib
import Lemma.Definitions.Def_FreyPackage_ModMCarrier_LatticeRed
import Lemma.Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Lemma.Definitions.Def_CuspForm_IntegralStructure
import Lemma.Definitions.Def_ModularForm_AtkinLehnerDatum

set_option autoImplicit false
noncomputable section
open CongruenceSubgroup ModularForm
open scoped TensorProduct

lemma CongruenceSubgroup.Gamma0_le_Gamma0_of_dvd {R M : ℕ} (hRM : R ∣ M) :
    Gamma0 M ≤ Gamma0 R := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have : ZMod.castHom hRM (ZMod R) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M)
      = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod R) := map_intCast _ _
  rw [← this, hγ, map_zero]

namespace FreyPackage.ModMCarrier

def levelInclusionLin {R M : ℕ} [NeZero M] (hRM : R ∣ M) (k : ℤ) :
    CuspForm (Gamma0 R) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun f :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ =>
        f.slash_action_eq' γ (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd hRM) hγ)
      holo' := f.holo'
      zero_at_cusps' := fun {c} hc => f.zero_at_cusps'
        (hc.mono (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd hRM))) }
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] lemma coe_levelInclusionLin {R M : ℕ} [NeZero M] (hRM : R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) : ⇑(levelInclusionLin hRM k f) = ⇑f := rfl

lemma _root_.ModularForm.AtkinLehnerDatum.R_dvd {M q' : ℕ} (W : ModularForm.AtkinLehnerDatum M q') :
    W.R ∣ M := ⟨q', W.hM.trans (Nat.mul_comm q' W.R)⟩

end FreyPackage.ModMCarrier

namespace FreyPackage.ModMCarrier

section WitnessResidueField

abbrev WitnessResidueField (𝔪 : Ideal (integralClosure ℤ ℂ)) : Type :=
  (integralClosure ℤ ℂ) ⧸ 𝔪

abbrev witnessResidueMap (𝔪 : Ideal (integralClosure ℤ ℂ)) :
    integralClosure ℤ ℂ →+* WitnessResidueField 𝔪 :=
  Ideal.Quotient.mk 𝔪

lemma witnessResidueMap_mem (𝔪 : Ideal (integralClosure ℤ ℂ)) :
    ∀ x ∈ 𝔪, witnessResidueMap 𝔪 x = 0 :=
  fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx

end WitnessResidueField

section OldSublattice
variable {M q' : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q')

local instance instNeZeroR : NeZero W.R :=
  ⟨fun h => NeZero.ne M (W.hM.trans (by rw [h, mul_zero]))⟩

def oldformSublattice : Submodule ℤ (CuspForm (Gamma0 M) 2) :=
  (CuspForm.intLattice W.R 2).map ((levelInclusionLin W.R_dvd 2).restrictScalars ℤ) ⊔
  (CuspForm.intLattice W.R 2).map ((rescaleLin W.q_mul_R_dvd 2).restrictScalars ℤ)

lemma levelInclusionLin_mem_oldformSublattice :
    ∀ x ∈ CuspForm.intLattice W.R 2,
      levelInclusionLin W.R_dvd 2 x ∈ oldformSublattice W :=
  fun _ hx => Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)

lemma rescaleLin_mem_oldformSublattice :
    ∀ x ∈ CuspForm.intLattice W.R 2,
      rescaleLin W.q_mul_R_dvd 2 x ∈ oldformSublattice W :=
  fun _ hx => Submodule.mem_sup_right (Submodule.mem_map_of_mem hx)

section ReducedMaps
variable (k : Type*) [Field k]

def f₀red {f : CuspForm (Gamma0 W.R) 2} (hf : f ∈ CuspForm.intLattice W.R 2) :
    latticeRed k (CuspForm.intLattice W.R 2) :=
  latticeRed.mk k _ ⟨f, hf⟩

def ι₀red : latticeRed k (CuspForm.intLattice W.R 2) →ₗ[k] latticeRed k (oldformSublattice W) :=
  latticeRed.mapOf k _ _ (levelInclusionLin W.R_dvd 2) (levelInclusionLin_mem_oldformSublattice W)

def ι₁red : latticeRed k (CuspForm.intLattice W.R 2) →ₗ[k] latticeRed k (oldformSublattice W) :=
  latticeRed.mapOf k _ _ (rescaleLin W.q_mul_R_dvd 2) (rescaleLin_mem_oldformSublattice W)

end ReducedMaps
end OldSublattice

section OfPrimeNotDvd
variable (N q' : ℕ)

def atkinLehnerDatumOfPrimeNotDvd (hq' : q'.Prime) (hnd : ¬ q' ∣ N) :
    ModularForm.AtkinLehnerDatum (N * q') q' where
  R := N
  hM := Nat.mul_comm N q'
  a := (Nat.gcdA q' N)
  b := -(Nat.gcdB q' N)
  bezout := by
    have hcop : Nat.gcd q' N = 1 := (hq'.coprime_iff_not_dvd).mpr hnd
    have hab := Nat.gcd_eq_gcd_ab q' N
    rw [hcop, Nat.cast_one] at hab
    push_cast
    linarith [hab]

@[simp] lemma atkinLehnerDatumOfPrimeNotDvd_R (hq' : q'.Prime) (hnd : ¬ q' ∣ N) :
    (atkinLehnerDatumOfPrimeNotDvd N q' hq' hnd).R = N := rfl

end OfPrimeNotDvd

end FreyPackage.ModMCarrier
