import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace HeckeEis

open CongruenceSubgroup Subgroup Matrix
open scoped MatrixGroups

section ConjMatrix

def alphaMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (ℓ : ℤ)]

@[simp] theorem alphaMat_apply_zero_zero (ℓ : ℕ) : alphaMat ℓ 0 0 = 1 := rfl
@[simp] theorem alphaMat_apply_zero_one (ℓ : ℕ) : alphaMat ℓ 0 1 = 0 := rfl
@[simp] theorem alphaMat_apply_one_zero (ℓ : ℕ) : alphaMat ℓ 1 0 = 0 := rfl
@[simp] theorem alphaMat_apply_one_one (ℓ : ℕ) : alphaMat ℓ 1 1 = (ℓ : ℤ) := rfl

theorem det_alphaMat (ℓ : ℕ) : (alphaMat ℓ).det = (ℓ : ℤ) := by
  rw [alphaMat, det_fin_two_of]; ring

theorem eq_of_mul_alphaMat_eq {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A * alphaMat ℓ = B * alphaMat ℓ) : A = B := by
  ext i j
  have h0 := congrFun (congrFun h i) 0
  have h1 := congrFun (congrFun h i) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    mul_one, mul_zero, add_zero, zero_add] at h0 h1
  fin_cases j
  · exact h0
  · exact mul_right_cancel₀ hℓ h1

def heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 / (ℓ : ℤ); g 1 0 * (ℓ : ℤ), g 1 1]

@[simp] theorem heckeConjMat_apply_zero_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 0 = g 0 0 := rfl
@[simp] theorem heckeConjMat_apply_zero_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 1 = g 0 1 / (ℓ : ℤ) := rfl
@[simp] theorem heckeConjMat_apply_one_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 0 = g 1 0 * (ℓ : ℤ) := rfl
@[simp] theorem heckeConjMat_apply_one_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 1 = g 1 1 := rfl

theorem heckeConjMat_mul_alphaMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) :
    heckeConjMat ℓ g * alphaMat ℓ = alphaMat ℓ * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
      alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
      heckeConjMat_apply_zero_zero, heckeConjMat_apply_zero_one, heckeConjMat_apply_one_zero,
      heckeConjMat_apply_one_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_zero,
      one_mul, zero_mul, add_zero, zero_add] <;>
    first
      | exact Int.ediv_mul_cancel hg
      | ring1

theorem dvd_mul_apply_zero_one {ℓ : ℕ} {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) : (ℓ : ℤ) ∣ (g * h) 0 1 := by
  rw [(Matrix.two_mul_expl g h).2.1]
  exact dvd_add (hh.mul_left _) (hg.mul_right _)

theorem heckeConjMat_mul {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) :
    heckeConjMat ℓ (g * h) = heckeConjMat ℓ g * heckeConjMat ℓ h := by
  have key : (heckeConjMat ℓ g * heckeConjMat ℓ h) * alphaMat ℓ = alphaMat ℓ * (g * h) := by
    rw [mul_assoc, heckeConjMat_mul_alphaMat hh, ← mul_assoc, heckeConjMat_mul_alphaMat hg,
      mul_assoc]
  exact eq_of_mul_alphaMat_eq hℓ
    ((heckeConjMat_mul_alphaMat (dvd_mul_apply_zero_one hg hh)).trans key.symm)

theorem det_heckeConjMat {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) : (heckeConjMat ℓ g).det = g.det := by
  have h := congrArg Matrix.det (heckeConjMat_mul_alphaMat hg)
  rw [Matrix.det_mul, Matrix.det_mul, det_alphaMat] at h
  exact mul_right_cancel₀ hℓ (by linear_combination h)

theorem heckeConjMat_one (ℓ : ℕ) : heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeConjMat]

theorem heckeConjMat_injective {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1)
    (e : heckeConjMat ℓ g = heckeConjMat ℓ h) : g = h := by
  have key : alphaMat ℓ * g = alphaMat ℓ * h := by
    rw [← heckeConjMat_mul_alphaMat hg, ← heckeConjMat_mul_alphaMat hh, e]
  ext i j
  have h0 := congrFun (congrFun key 0) j
  have h1 := congrFun (congrFun key 1) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    one_mul, zero_mul, add_zero, zero_add] at h0 h1
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ hℓ h1

end ConjMatrix

section HeckeSubgroup

def heckeUpperSL (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {g | (ℓ : ℤ) ∣ g 0 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h : (ℓ : ℤ) ∣ (a.1 * b.1) 0 1 := by
      rw [(Matrix.two_mul_expl a.1 b.1).2.1]
      exact dvd_add (hb.mul_left _) (ha.mul_right _)
    exact h
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simpa using ha

@[simp]
theorem mem_heckeUpperSL {ℓ : ℕ} {g : SL(2, ℤ)} : g ∈ heckeUpperSL ℓ ↔ (ℓ : ℤ) ∣ g 0 1 :=
  Iff.rfl

variable (N ℓ : ℕ)

def heckeUpper : Subgroup (Gamma0 N) := (heckeUpperSL ℓ).subgroupOf (Gamma0 N)

theorem mem_heckeUpper {γ : Gamma0 N} :
    γ ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
  Iff.rfl

def gammaZeroRed : Gamma0 N →* SL(2, ZMod ℓ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod ℓ))).comp
    (Gamma0 N).subtype

theorem ker_gammaZeroRed_le_heckeUpper : (gammaZeroRed N ℓ).ker ≤ heckeUpper N ℓ := by
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  rw [mem_heckeUpper]
  have h01 : ((((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) = 0 := by
    have h := congrArg (fun A : SL(2, ZMod ℓ) => A 0 1) hγ
    simpa [gammaZeroRed, Matrix.one_apply] using h
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h01

instance instFiniteIndexHeckeUpper [NeZero ℓ] : (heckeUpper N ℓ).FiniteIndex :=
  haveI : (gammaZeroRed N ℓ).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  Subgroup.finiteIndex_of_le (ker_gammaZeroRed_le_heckeUpper N ℓ)

variable [NeZero ℓ]

def heckeConjSL (γ : heckeUpper N ℓ) : SL(2, ℤ) :=
  ⟨heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)), by
    rw [det_heckeConjMat (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)]
    exact ((γ : Gamma0 N) : SL(2, ℤ)).2⟩

@[simp]
theorem coe_heckeConjSL (γ : heckeUpper N ℓ) :
    (heckeConjSL N ℓ γ : Matrix (Fin 2) (Fin 2) ℤ) =
      heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)) :=
  rfl

theorem heckeConjSL_mem_Gamma0 (γ : heckeUpper N ℓ) : heckeConjSL N ℓ γ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show (((heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ))) 1 0 : ℤ) : ZMod N) = 0
  rw [heckeConjMat_apply_one_zero, Int.cast_mul]
  have hc : ((((γ : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp (γ : Gamma0 N).2
  rw [hc, zero_mul]

def heckeConj : heckeUpper N ℓ →* Gamma0 N where
  toFun γ := ⟨heckeConjSL N ℓ γ, heckeConjSL_mem_Gamma0 N ℓ γ⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = (1 : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_one ℓ
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ
        ((((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      heckeConjMat ℓ (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        heckeConjMat ℓ (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_mul (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
      ((mem_heckeUpper N ℓ).mp γ.2) ((mem_heckeUpper N ℓ).mp δ.2)

@[simp]
theorem coe_heckeConj (γ : heckeUpper N ℓ) :
    ((heckeConj N ℓ γ : Gamma0 N) : SL(2, ℤ)) = heckeConjSL N ℓ γ :=
  rfl

theorem heckeConj_injective : Function.Injective (heckeConj N ℓ) := by
  intro γ δ h
  have hmat : heckeConjMat ℓ (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      heckeConjMat ℓ (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    congrArg (fun x : Gamma0 N => ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h
  exact Subtype.ext (Subtype.ext (Subtype.ext (heckeConjMat_injective
    (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)
    ((mem_heckeUpper N ℓ).mp δ.2) hmat)))

end HeckeSubgroup

section Transfer

variable {G : Type*} [Group G] (H : Subgroup G) {A : Type*} [AddCommGroup A]

def resHom : (Additive G →+ A) →+ (Additive H →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive H.subtype)) fun _ _ => rfl

@[simp]
theorem resHom_apply (φ : Additive G →+ A) (γ : H) :
    resHom H φ (Additive.ofMul γ) = φ (Additive.ofMul (γ : G)) :=
  rfl

noncomputable def transferAux (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

@[simp]
theorem coe_transferAux (g : G) (q : G ⧸ H) :
    (transferAux H g q : G) = (g • q).out⁻¹ * (g * q.out) :=
  rfl

theorem transferAux_mul (g₁ g₂ : G) (q : G ⧸ H) :
    transferAux H (g₁ * g₂) q = transferAux H g₁ (g₂ • q) * transferAux H g₂ q := by
  ext
  push_cast [coe_transferAux]
  rw [mul_smul]
  group

variable [H.FiniteIndex]

noncomputable def coresHom : (Additive H →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk'
    (fun φ =>
      letI := H.fintypeQuotientOfFiniteIndex
      AddMonoidHom.mk'
        (fun g => ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g.toMul q)))
        (fun g₁ g₂ => by
          show ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H (g₁.toMul * g₂.toMul) q)) =
            (∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g₁.toMul q))) +
              ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g₂.toMul q))
          simp_rw [transferAux_mul, ofMul_mul, map_add]
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (· + ·)
            (Fintype.sum_bijective (g₂.toMul • ·) (MulAction.bijective g₂.toMul)
              (fun q => φ (Additive.ofMul (transferAux H g₁.toMul (g₂.toMul • q))))
              (fun q => φ (Additive.ofMul (transferAux H g₁.toMul q))) fun q => rfl) rfl))
    (fun φ ψ => by
      letI := H.fintypeQuotientOfFiniteIndex
      ext g
      exact Finset.sum_add_distrib)

theorem coresHom_apply (φ : Additive H →+ A) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) :=
  rfl

end Transfer

section Pullback

variable {G K : Type*} [Group G] [Group K] {A : Type*} [AddCommGroup A]

def pullbackHom (f : G →* K) : (Additive K →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive f)) fun _ _ => rfl

@[simp]
theorem pullbackHom_apply (f : G →* K) (φ : Additive K →+ A) (g : G) :
    pullbackHom f φ (Additive.ofMul g) = φ (Additive.ofMul (f g)) :=
  rfl

end Pullback

section HeckeOperator

variable (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]

noncomputable def heckeOperatorHom :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (coresHom (heckeUpper N ℓ)).comp (pullbackHom (heckeConj N ℓ))

theorem heckeOperatorHom_apply (φ : Additive (Gamma0 N) →+ A) (g : Gamma0 N) :
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    heckeOperatorHom N ℓ A φ (Additive.ofMul g) =
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        φ (Additive.ofMul ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N))) :=
  rfl

noncomputable abbrev uOperatorHom (q : ℕ) [NeZero q] :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  heckeOperatorHom N q A

def HeckeIndexEq : Prop := (heckeUpper N ℓ).index = ℓ + 1

end HeckeOperator

end HeckeEis
