import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Def.ModularCurve_PeriodMap
import Instance.ModularCurve_PDPairing
import Abbrev.ModularCurve_PDPairing

set_option autoImplicit false

namespace Matrix.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section Cores
variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

noncomputable def coresAdd (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive ↥K →+ B) : Additive G →+ B :=
  MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ))

end Cores

section ConjMats

variable (ℓ d : ℕ)

def conjUpperMat (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 / ℓ * (A 1 0 * ℓ) = A 0 1 * A 1 0 := by
      rw [mul_comm (A 1 0) _, ← mul_assoc, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

def conjLowerMat (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 * d; A 1 0 / d, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 * d * (A 1 0 / d) = A 0 1 * A 1 0 := by
      rw [mul_assoc, mul_comm (d : ℤ) _, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

end ConjMats

section Gamma0Legs

variable (M M' d : ℕ)

def iotaDeg0 [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) : ↥(Gamma0 M') →* ↥(Gamma0 M) where
  toFun γ := ⟨conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ),
    conjLowerMat_mem0 M M' d hMM' hdd γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjLowerMat]
  map_mul' γ δ :=
    Subtype.ext (conjLowerMat_mul d (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ)
      (dvd_entry0 M M' d hMM' hdd δ) (dvd_entry0 M M' d hMM' hdd (γ * δ)))

def iDeg0 (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Additive ↥(Gamma0 M) →+ A) →ₗ[R] (Additive ↥(Gamma0 M') →+ A) where
  toFun φ := φ.comp (MonoidHom.toAdditive (iotaDeg0 M M' d hMM' hdd))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

noncomputable def pushChar0 (A : Type*) [AddCommGroup A] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) (φ : Additive ↥(Gamma0 M') →+ A) :
    Additive ↥((iotaDeg0 M M' d hMM' hdd).range) →+ A :=
  φ.comp (MonoidHom.toAdditive
    ((iotaDeg0 M M' d hMM' hdd).ofInjective (iotaDeg0_injective M M' d hMM' hdd)).symm.toMonoidHom)

noncomputable def jDeg0 (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]
    [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Additive ↥(Gamma0 M') →+ A) →ₗ[R] (Additive ↥(Gamma0 M) →+ A) where
  toFun φ := coresAdd _ (pushChar0 M M' d A hMM' hdd φ)
  map_add' φ ψ := by
    have : pushChar0 M M' d A hMM' hdd (φ + ψ)
        = pushChar0 M M' d A hMM' hdd φ + pushChar0 M M' d A hMM' hdd ψ := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : pushChar0 M M' d A hMM' hdd (r • φ) = r • pushChar0 M M' d A hMM' hdd φ := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

end Gamma0Legs

section Gamma0Hecke

variable (M : ℕ)

def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, Int.cast_neg, neg_eq_zero] at *
    exact ha

variable (ℓ : ℕ)

abbrev Gamma0HUpper : Subgroup ↥(Gamma0 M) := (Gamma0Upper ℓ).subgroupOf (Gamma0 M)

def conjL0 : ↥(Gamma0HUpper M ℓ) →* ↥(Gamma0 M) where
  toFun γ := ⟨conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ γ),
    conjUpperMat_mem0 M ℓ γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjUpperMat]
  map_mul' γ δ :=
    Subtype.ext (conjUpperMat_mul ℓ (γ : SL(2, ℤ)) (δ : SL(2, ℤ))
      (dvd_of_mem_Gamma0HUpper M ℓ γ) (dvd_of_mem_Gamma0HUpper M ℓ δ)
      (dvd_of_mem_Gamma0HUpper M ℓ (γ * δ)))

variable (A : Type*) [AddCommGroup A]

noncomputable def heckeT0 [NeZero ℓ] :
    (Additive ↥(Gamma0 M) →+ A) →+ (Additive ↥(Gamma0 M) →+ A) where
  toFun φ :=
    MonoidHom.toAdditiveLeft
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ)))
  map_zero' := by
    simp only [toMultiplicativeRight_zero, MonoidHom.one_comp,
      transfer_one, toAdditiveLeft_one]
  map_add' φ ψ := by
    simp only [toMultiplicativeRight_add, MonoidHom.mul_comp,
      transfer_mul, toAdditiveLeft_mul]

end Gamma0Hecke

section Prim
variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

def omega (φ ψ : Additive Φ →+ R) (g g' : Φ) : R :=
  φ (Additive.ofMul g) * ψ (Additive.ofMul g') - ψ (Additive.ofMul g) * φ (Additive.ofMul g')

def CentralExt (_φ _ψ : Additive Φ →+ R) : Type _ := R × Φ

namespace CentralExt

variable (φ ψ : Additive Φ →+ R)

def snd : CentralExt φ ψ →* Φ where
  toFun x := x.2
  map_one' := rfl
  map_mul' _ _ := rfl

end CentralExt

variable [IsFreeGroup Φ]

noncomputable def sect (φ ψ : Additive Φ →+ R) : Φ →* CentralExt φ ψ :=
  IsFreeGroup.lift (fun a => (((0 : R), IsFreeGroup.of a) : CentralExt φ ψ))

noncomputable def hPrim (φ ψ : Additive Φ →+ R) (g : Φ) : R := (sect φ ψ g).1

def CentralExt.lift (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g') : Φ →* CentralExt φ ψ where
  toFun g := (H g, g)
  map_one' := by
    have h := hH 1 1
    rw [one_mul, omega_one_left, sub_zero] at h
    have h1 : H 1 = 0 := by linear_combination -h
    rw [h1]
    rfl
  map_mul' g g' := by
    rw [CentralExt.mul_def]
    exact Prod.ext (hH g g') rfl

omit [IsFreeGroup Φ] in
end Prim

section Cusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]

noncomputable def cuspGen (q : Cusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩

noncomputable def cuspSum (f : Φ → R) : R := ∑ q : Cusp Φ, f (cuspGen Φ q)

noncomputable def pairF [IsFreeGroup Φ] [Invertible (2 : R)] (φ ψ : Additive Φ →+ R) : R :=
  ⅟(2 : R) * cuspSum Φ (hPrim φ ψ)

end Cusps

section Descent

variable (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ]
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {R : Type*} [CommRing R]

def resInf (φ : Additive Γ →+ R) : Additive ↥(Γ ⊓ Λ) →+ R :=
  φ.comp (MonoidHom.toAdditive (Subgroup.inclusion (inf_le_left : Γ ⊓ Λ ≤ Γ)))

noncomputable def pairD [Invertible (2 : R)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) : R :=
  ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * pairF (Γ ⊓ Λ) (resInf Λ Γ φ) (resInf Λ Γ ψ)

end Descent

section LevelZ

open ModularCurve.Period

variable (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]

noncomputable def pairZFun (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) : ℤ :=
  ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : ℤ) *
    cuspSum (Gamma0 N ⊓ Gamma 4) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ))

noncomputable def pairZ :
    parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => pairZFun N (x : Additive ↥(Gamma0 N) →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ))
    (fun x₁ x₂ y => by
      rw [Submodule.coe_add, pairZFun_add_left])
    (fun r x y => by
      rw [Submodule.coe_smul, pairZFun_smul_left, smul_eq_mul])
    (fun x y₁ y₂ => by
      rw [Submodule.coe_add, pairZFun_add_right])
    (fun r x y => by
      rw [Submodule.coe_smul, pairZFun_smul_right, smul_eq_mul])

end LevelZ

end Matrix.PDPairing
