import Mathlib
import Lemma.ModularCurve.TateFormal
import Structure.ModularForm_KatzLevelOne

universe u

noncomputable section

open WeierstrassCurve


namespace KatzModularForm

variable {R : Type u} [CommRing R] {k l : ℤ}

theorem isUnit_Δ_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {W : WeierstrassCurve A} (hW : IsUnit W.Δ) : IsUnit (W.map f).Δ := by
  rw [WeierstrassCurve.map_Δ]; exact hW.map f

theorem isUnit_Δ_variableChange {A : Type*} [CommRing A] (C : VariableChange A)
    {W : WeierstrassCurve A} (hW : IsUnit W.Δ) : IsUnit (C • W).Δ := by
  rw [WeierstrassCurve.variableChange_Δ]
  exact ((C.u⁻¹).isUnit.pow 12).mul hW

theorem toFun_injective : Function.Injective (toFun : KatzModularForm R k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr

@[ext]
theorem ext {F G : KatzModularForm R k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = G.toFun W hW) : F = G :=
  toFun_injective (by funext A _ _ W hW; exact h W hW)


@[simp] theorem zero_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (0 : KatzModularForm R k).toFun W hW = 0 := rfl

@[simp] theorem add_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F + G).toFun W hW = F.toFun W hW + G.toFun W hW := rfl

@[simp] theorem neg_toFun (F : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) : (-F).toFun W hW = -F.toFun W hW := rfl

@[simp] theorem sub_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F - G).toFun W hW = F.toFun W hW - G.toFun W hW := rfl

@[simp] theorem smul_toFun (c : R) (F : KatzModularForm R k) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (c • F).toFun W hW = c • F.toFun W hW := rfl


def mul (F : KatzModularForm R k) (G : KatzModularForm R l) : KatzModularForm R (k + l) where
  toFun _ _ _ W hW := F.toFun W hW * G.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    rw [map_mul, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', zpow_add,
      Units.val_mul]
    ring

@[simp] theorem mul_toFun (F : KatzModularForm R k) (G : KatzModularForm R l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F.mul G).toFun W hW = F.toFun W hW * G.toFun W hW := rfl

def qExpansion (F : KatzModularForm R k) : LaurentSeries R :=
  F.toFun (ModularCurve.tateLaurent R) (ModularCurve.tateLaurent R).isUnit_Δ

@[simp] theorem qExpansion_zero : (0 : KatzModularForm R k).qExpansion = 0 := rfl

@[simp] theorem qExpansion_add (F G : KatzModularForm R k) :
    (F + G).qExpansion = F.qExpansion + G.qExpansion := rfl

@[simp] theorem qExpansion_neg (F : KatzModularForm R k) : (-F).qExpansion = -F.qExpansion := rfl

@[simp] theorem qExpansion_sub (F G : KatzModularForm R k) :
    (F - G).qExpansion = F.qExpansion - G.qExpansion := rfl

@[simp] theorem qExpansion_smul (c : R) (F : KatzModularForm R k) :
    (c • F).qExpansion = c • F.qExpansion := by
  simp only [qExpansion, smul_toFun, Algebra.smul_def, ← HahnSeries.C_mul_eq_smul]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  simp

@[simp] theorem qExpansion_mul (F : KatzModularForm R k) (G : KatzModularForm R l) :
    (F.mul G).qExpansion = F.qExpansion * G.qExpansion := rfl

variable (R)

def c₄ : KatzModularForm R 4 where
  toFun _ _ _ W _ := W.c₄
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₄ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₄ C]
    norm_cast

def c₆ : KatzModularForm R 6 where
  toFun _ _ _ W _ := W.c₆
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₆ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₆ C]
    norm_cast

def discr : KatzModularForm R 12 where
  toFun _ _ _ W _ := W.Δ
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_Δ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_Δ C]
    norm_cast

variable {R}

@[simp] theorem c₄_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₄ R).toFun W hW = W.c₄ := rfl

@[simp] theorem c₆_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₆ R).toFun W hW = W.c₆ := rfl

@[simp] theorem discr_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (discr R).toFun W hW = W.Δ := rfl

theorem qExpansion_c₄ : (c₄ R).qExpansion = (ModularCurve.tateLaurent R).c₄ := rfl

theorem qExpansion_c₆ : (c₆ R).qExpansion = (ModularCurve.tateLaurent R).c₆ := rfl

theorem qExpansion_discr : (discr R).qExpansion = (ModularCurve.tateLaurent R).Δ := rfl

end KatzModularForm

end
