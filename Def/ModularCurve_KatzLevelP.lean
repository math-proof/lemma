module

public import Mathlib
public import Instance.ModularForm_KatzLevelOne
public import Instance.ModularCurve_KatzLevelP
public import Structure.ModularCurve_KatzLevelP

@[expose] public section

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve


namespace LevelPData

variable {A : Type u} {B : Type v}

def swap (D : LevelPData A) : LevelPData A :=
  ⟨D.xQ, D.yQ, D.xP, D.yP⟩

variable [CommRing A] [CommRing B]

def map (f : A →+* B) (D : LevelPData A) : LevelPData B :=
  ⟨f D.xP, f D.yP, f D.xQ, f D.yQ⟩

end LevelPData


namespace IsLevelPStructure

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {p : ℕ}
  {D : LevelPData A}

end IsLevelPStructure


namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

section simp_lemmas

variable {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
  (D : LevelPData A) (hD : IsLevelPStructure W p D)

end simp_lemmas

def mul (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) : KatzLevelPForm R p (k + l) where
  toFun _ _ _ W hW D hD := F.toFun W hW D hD * G.toFun W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    rw [map_mul, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    rw [F.toFun_variableChange C W hW hW' D hD hD', G.toFun_variableChange C W hW hW' D hD hD',
      zpow_add, Units.val_mul]
    ring

def swap (F : KatzLevelPForm R p k) : KatzLevelPForm R p k where
  toFun _ _ _ W hW D hD := F.toFun W hW D.swap hD.swap
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact F.map_toFun f W hW hW' D.swap hD.swap hD'.swap
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact F.toFun_variableChange C W hW hW' D.swap hD.swap hD'.swap

def DependsOnlyOnLines (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xP D'.xP → InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD

def SwapInvariant (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D),
    F.toFun W hW D.swap hD.swap = F.toFun W hW D hD

end KatzLevelPForm


namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

def mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) : KatzGamma0Form R p (k + l) :=
  ⟨F.toKatzLevelPForm.mul G.toKatzLevelPForm, F.dependsOnlyOnSndLine.mul G.dependsOnlyOnSndLine⟩

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k : ℤ}

def pullbackLevelP (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzLevelPForm R p k where
  toFun _ _ _ W hW _ _ := g.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact g.map_toFun f W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact g.toFun_variableChange C W hW hW'

def pullbackGamma0 (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzGamma0Form R p k :=
  ⟨g.pullbackLevelP p, g.dependsOnlyOnSndLine_pullbackLevelP p⟩

end KatzModularForm

namespace ModularCurve.LevelP

variable (p : ℕ)

def borel : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh, zero_mul, mul_zero, add_zero]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
    simp [hg]

def splitTorus : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg.1, hh.1, hg.2, hh.2]
    simp
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.adjugate_fin_two]
    simp [hg.1, hg.2]

def unipotentU : GL (Fin 2) (ZMod p) :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

def swapW : GL (Fin 2) (ZMod p) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

end ModularCurve.LevelP

end

end
