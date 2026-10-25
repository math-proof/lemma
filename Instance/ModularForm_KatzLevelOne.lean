-- Carved from Lemma/Definitions/Def_ModularForm_KatzLevelOne.lean: instance decls only.
import Mathlib

universe u

noncomputable section

open WeierstrassCurve


namespace KatzModularForm

variable {R : Type u} [CommRing R] {k l : ℤ}


instance : Zero (KatzModularForm R k) :=
  ⟨{ toFun := fun _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW + G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_add, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_add] }⟩

instance : Neg (KatzModularForm R k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW => -F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_neg, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_neg] }⟩

instance : Sub (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW - G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_sub, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_sub] }⟩

instance : SMul R (KatzModularForm R k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW => c • F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_smul, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_smul_comm] }⟩


instance : AddCommGroup (KatzModularForm R k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzModularForm R k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp


end KatzModularForm

end
