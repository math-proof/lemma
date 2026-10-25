import Mathlib
import Def.ModularCurve_WeierstrassLevelModuliDatum
import Lemma.ModularCurve.KatzLevelP
import Structure.ModularCurve_WeierstrassLevelComponents

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve


namespace LevelComponent

variable {A : Type u} [CommRing A]

def trivial : LevelComponent A where
  obj _ _ _ := PUnit
  IsLevel _ _ := True
  map _ x := x
  act _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one _ := rfl
  act_mul _ _ _ := rfl
  map_act _ _ _ := rfl
  isLevel_map _ _ _ h := h
  isLevel_act _ _ _ h := h

def prod (L₁ L₂ : LevelComponent A) : LevelComponent A where
  obj T _ _ := L₁.obj T × L₂.obj T
  IsLevel W x := L₁.IsLevel W x.1 ∧ L₂.IsLevel W x.2
  map f x := (L₁.map f x.1, L₂.map f x.2)
  act C x := (L₁.act C x.1, L₂.act C x.2)
  map_id x := Prod.ext (L₁.map_id x.1) (L₂.map_id x.2)
  map_comp f g x := Prod.ext (L₁.map_comp f g x.1) (L₂.map_comp f g x.2)
  act_one x := Prod.ext (L₁.act_one x.1) (L₂.act_one x.2)
  act_mul C C' x := Prod.ext (L₁.act_mul C C' x.1) (L₂.act_mul C C' x.2)
  map_act f C x := Prod.ext (L₁.map_act f C x.1) (L₂.map_act f C x.2)
  isLevel_map f W x h := ⟨L₁.isLevel_map f W x.1 h.1, L₂.isLevel_map f W x.2 h.2⟩
  isLevel_act C W x h := ⟨L₁.isLevel_act C W x.1 h.1, L₂.isLevel_act C W x.2 h.2⟩


theorem Raw.ext' {L : LevelComponent A} {T : Type u} [CommRing T] [Algebra A T] {x y : L.Raw T}
    (h₁ : x.curve = y.curve) (h₂ : x.level = y.level) : x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

def toRigid (L : LevelComponent A) : RigidWeierstrassData.{u} A where
  Raw T _ _ := L.Raw T
  curve x := x.curve
  isUnit_Δ x := x.isUnit_Δ
  mapRing f x := ⟨x.curve.map f.toRingHom, x.curve.isUnit_Δ_map f.toRingHom x.isUnit_Δ, L.map f x.level,
    L.isLevel_map f _ _ x.isLevel⟩
  curve_mapRing _ _ := rfl
  mapRing_id x := Raw.ext' (x.curve.map_id) (L.map_id x.level)
  mapRing_comp f g x := Raw.ext' (x.curve.map_map f.toRingHom g.toRingHom).symm (L.map_comp f g x.level)
  act C x := ⟨C • x.curve, x.curve.isUnit_Δ_variableChange C x.isUnit_Δ, L.act C x.level,
    L.isLevel_act C _ _ x.isLevel⟩
  act_one x := Raw.ext' (one_smul _ _) (L.act_one x.level)
  act_mul C C' x := Raw.ext' (mul_smul C C' _) (L.act_mul C C' x.level)
  curve_act _ _ := rfl
  mapRing_act f C x := Raw.ext' (x.curve.map_variableChange C f.toRingHom).symm (L.map_act f C x.level)

end LevelComponent

section Gamma0

variable {T : Type u} [CommRing T]

def kernelVariableChangeDeg (C : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) : T[X] :=
  Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) *
    h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r)

theorem kernelVariableChangeDeg_eq_kernelVariableChange (C : WeierstrassCurve.VariableChange T) (h : T[X]) :
    kernelVariableChangeDeg C h.natDegree h = WeierstrassCurve.kernelVariableChange C h := rfl

theorem kernelVariableChangeDeg_one (d : ℕ) (h : T[X]) :
    kernelVariableChangeDeg (1 : WeierstrassCurve.VariableChange T) d h = h := by
  simp [kernelVariableChangeDeg, WeierstrassCurve.VariableChange.one_def]

theorem kernelVariableChangeDeg_mul (C C' : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) :
    kernelVariableChangeDeg (C * C') d h = kernelVariableChangeDeg C d (kernelVariableChangeDeg C' d h) := by
  simp only [kernelVariableChangeDeg, WeierstrassCurve.VariableChange.mul_def, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp,
    mul_inv, Units.val_mul, mul_pow, map_mul, map_pow, map_add]
  have hin : (Polynomial.C ((C'.u : Tˣ) : T) ^ 2 * (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r) +
      Polynomial.C C'.r : T[X]) = Polynomial.C ((C.u : Tˣ) : T) ^ 2 * Polynomial.C ((C'.u : Tˣ) : T) ^ 2 * X +
      (Polynomial.C C.r * Polynomial.C ((C'.u : Tˣ) : T) ^ 2 + Polynomial.C C'.r) := by ring
  rw [hin]; ring

theorem kernelVariableChangeDeg_map {T' : Type u} [CommRing T'] (f : T →+* T')
    (C : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) :
    (kernelVariableChangeDeg C d h).map f = kernelVariableChangeDeg (C.map f) d (h.map f) := by
  simp only [kernelVariableChangeDeg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, WeierstrassCurve.VariableChange.map,
    map_pow, Units.coe_map_inv, Units.coe_map, MonoidHom.coe_coe]

end Gamma0

def gamma0Component (A : Type u) [CommRing A] (N : ℕ)
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : T[X]), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (kernelVariableChangeDeg C ((N - 1) / 2) h)) :
    LevelComponent A where
  obj T _ _ := T[X]
  IsLevel W h := W.IsCyclicKernel N h
  map f h := h.map f.toRingHom
  act C h := kernelVariableChangeDeg C ((N - 1) / 2) h
  map_id _ := Polynomial.map_id
  map_comp f g h := (Polynomial.map_map f.toRingHom g.toRingHom h).symm
  act_one h := kernelVariableChangeDeg_one _ h
  act_mul C C' h := kernelVariableChangeDeg_mul C C' _ h
  map_act f C h := kernelVariableChangeDeg_map f.toRingHom C _ h
  isLevel_map f W _ hh := WeierstrassCurve.IsCyclicKernel.map W f.toRingHom hh
  isLevel_act C W h hh := hN _ W C h hh

section LevelP

variable {T : Type u} [CommRing T]

theorem LevelPData.variableChange_one (D : LevelPData T) :
    D.variableChange (1 : WeierstrassCurve.VariableChange T) = D := by
  ext <;> simp [LevelPData.variableChange, WeierstrassCurve.VariableChange.one_def]

theorem LevelPData.variableChange_mul (C C' : WeierstrassCurve.VariableChange T) (D : LevelPData T) :
    D.variableChange (C * C') = (D.variableChange C').variableChange C := by
  set v : T := ((C.u⁻¹ : Tˣ) : T) with hv
  set v' : T := ((C'.u⁻¹ : Tˣ) : T) with hv'
  set u' : T := ((C'.u : Tˣ) : T) with hu'
  have h1 : v' * u' = 1 := by rw [hv', hu', Units.inv_mul]
  have h2 : v' ^ 2 * u' ^ 2 = 1 := by rw [← mul_pow, h1, one_pow]
  have h3 : v' ^ 3 * u' ^ 3 = 1 := by rw [← mul_pow, h1, one_pow]
  ext <;> simp only [LevelPData.variableChange, WeierstrassCurve.VariableChange.mul_def, mul_inv, Units.val_mul,
      mul_pow, ← hv, ← hv', ← hu']
  · linear_combination (-(v ^ 2) * C.r) * h2
  · linear_combination (-(v ^ 3) * C.s * (D.xP - C'.r) * v' ^ 2) * h1 + (v ^ 3 * (C.s * C.r - C.t)) * h3
  · linear_combination (-(v ^ 2) * C.r) * h2
  · linear_combination (-(v ^ 3) * C.s * (D.xQ - C'.r) * v' ^ 2) * h1 + (v ^ 3 * (C.s * C.r - C.t)) * h3

theorem LevelPData.map_variableChange {T' : Type u} [CommRing T'] (f : T →+* T')
    (C : WeierstrassCurve.VariableChange T) (D : LevelPData T) :
    (D.variableChange C).map f = (D.map f).variableChange (C.map f) := by
  ext <;> simp [LevelPData.variableChange, LevelPData.map, WeierstrassCurve.VariableChange.map, map_mul, map_sub,
    map_pow]

end LevelP

def levelPComponent (A : Type u) [CommRing A] (ℓ : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsLevelPStructure W ℓ D → IsLevelPStructure (C • W) ℓ (D.variableChange C)) :
    LevelComponent A where
  obj T _ _ := LevelPData T
  IsLevel W D := IsLevelPStructure W ℓ D
  map f D := D.map f.toRingHom
  act C D := D.variableChange C
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one D := LevelPData.variableChange_one D
  act_mul C C' D := LevelPData.variableChange_mul C C' D
  map_act f C D := LevelPData.map_variableChange f.toRingHom C D
  isLevel_map f _ _ hD := hD.map f.toRingHom
  isLevel_act C W D hD := hℓ _ W C D hD

def weierstrassLevelRigidData (A : Type u) [CommRing A] (ℓ N : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsLevelPStructure W ℓ D → IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : T[X]), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (kernelVariableChangeDeg C ((N - 1) / 2) h))
    (Dq : LevelComponent A) : RigidWeierstrassData.{u} A :=
  ((gamma0Component A N hN).prod ((levelPComponent A ℓ hℓ).prod Dq)).toRigid

end ModularCurve

end
