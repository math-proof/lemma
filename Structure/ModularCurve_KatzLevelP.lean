import Mathlib
import Instance.ModularForm_KatzLevelOne
import Instance.ModularCurve_KatzLevelP

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

section Elements

variable {A : Type*} [CommRing A]

def indepElt (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : A :=
  ∏ a ∈ Finset.Icc 1 ((p - 1) / 2), (x * (W.ΨSq a).eval x₀ - (W.Φ a).eval x₀)

def InLine (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ (p - 1) / 2 ∧ x * (W.ΨSq a).eval x₀ = (W.Φ a).eval x₀


end Elements

@[ext]
structure LevelPData (A : Type u) where

  xP : A

  yP : A

  xQ : A

  yQ : A

namespace LevelPData

variable {A : Type u} {B : Type v}


variable [CommRing A] [CommRing B]


def variableChange (C : VariableChange A) (D : LevelPData A) : LevelPData A where
  xP := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r)
  yP := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t)
  xQ := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r)
  yQ := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t)


end LevelPData

structure IsLevelPStructure {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ)
    (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  equation_Q : W.toAffine.Equation D.xQ D.yQ

  preΨ_P : (W.preΨ p).eval D.xP = 0

  preΨ_Q : (W.preΨ p).eval D.xQ = 0

  isUnit_indepElt_PQ : IsUnit (indepElt W p D.xP D.xQ)

  isUnit_indepElt_QP : IsUnit (indepElt W p D.xQ D.xP)

namespace IsLevelPStructure

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {p : ℕ}
  {D : LevelPData A}


end IsLevelPStructure

structure KatzLevelPForm (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ →
    ∀ D : LevelPData A, IsLevelPStructure W p D → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure (W.map (f : A →+* B)) p (D.map (f : A →+* B))),
    toFun (W.map (f : A →+* B)) hW' (D.map (f : A →+* B)) hD' = f (toFun W hW D hD)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure (C • W) p (D.variableChange C)),
    toFun (C • W) hW' (D.variableChange C) hD' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW D hD

namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}


section simp_lemmas

variable {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
  (D : LevelPData A) (hD : IsLevelPStructure W p D)


end simp_lemmas


def DependsOnlyOnSndLine (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD


end KatzLevelPForm

structure KatzGamma0Form (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1)
    extends KatzLevelPForm R p k where

  dependsOnlyOnSndLine : toKatzLevelPForm.DependsOnlyOnSndLine

namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}


end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k : ℤ}


end KatzModularForm

namespace ModularCurve.LevelP

variable (p : ℕ)


end ModularCurve.LevelP

end
