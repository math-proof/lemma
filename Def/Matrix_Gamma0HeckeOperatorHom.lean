module
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Instance.Gamma0HeckeOperatorHom


public section

namespace HeckeEis

open CongruenceSubgroup Subgroup Matrix
open scoped MatrixGroups

section ConjMatrix

def alphaMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (ℓ : ℤ)]

def heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 / (ℓ : ℤ); g 1 0 * (ℓ : ℤ), g 1 1]

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

variable (N ℓ : ℕ)

def heckeUpper : Subgroup (Gamma0 N) := (heckeUpperSL ℓ).subgroupOf (Gamma0 N)

def gammaZeroRed : Gamma0 N →* SL(2, ZMod ℓ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod ℓ))).comp
    (Gamma0 N).subtype

variable [NeZero ℓ]

def heckeConjSL (γ : heckeUpper N ℓ) : SL(2, ℤ) :=
  ⟨heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)), by
    rw [det_heckeConjMat (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)]
    exact ((γ : Gamma0 N) : SL(2, ℤ)).2⟩

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

end HeckeSubgroup

section Transfer

variable {G : Type*} [Group G] (H : Subgroup G) {A : Type*} [AddCommGroup A]

def resHom : (Additive G →+ A) →+ (Additive H →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive H.subtype)) fun _ _ => rfl

noncomputable def transferAux (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

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

end Transfer

section Pullback

variable {G K : Type*} [Group G] [Group K] {A : Type*} [AddCommGroup A]

def pullbackHom (f : G →* K) : (Additive K →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive f)) fun _ _ => rfl

end Pullback

section HeckeOperator

variable (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]

noncomputable def heckeOperatorHom :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (coresHom (heckeUpper N ℓ)).comp (pullbackHom (heckeConj N ℓ))

noncomputable abbrev uOperatorHom (q : ℕ) [NeZero q] :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  heckeOperatorHom N q A

def HeckeIndexEq : Prop := (heckeUpper N ℓ).index = ℓ + 1

end HeckeOperator

end HeckeEis
