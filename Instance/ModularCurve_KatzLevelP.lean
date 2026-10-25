-- Carved from Lemma/Definitions/Def_ModularCurve_KatzLevelP.lean: instance decls only.
import Mathlib
import Instance.ModularForm_KatzLevelOne
import Lemma.ModularCurve.KatzLevelP

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve


namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

instance : Zero (KatzLevelPForm R p k) :=
  ⟨{ toFun := fun _ _ _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD + G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_add, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_add] }⟩

instance : Neg (KatzLevelPForm R p k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW D hD => -F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_neg, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_neg] }⟩

instance : Sub (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD - G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_sub, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_sub] }⟩

instance : SMul R (KatzLevelPForm R p k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW D hD => c • F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_smul, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_smul_comm] }⟩


instance : AddCommGroup (KatzLevelPForm R p k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzLevelPForm R p k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

end KatzLevelPForm

namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

instance : Zero (KatzGamma0Form R p k) := ⟨⟨0, KatzLevelPForm.DependsOnlyOnSndLine.zero⟩⟩

instance : Add (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm + G.toKatzLevelPForm,
    F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine⟩⟩

instance : Neg (KatzGamma0Form R p k) :=
  ⟨fun F => ⟨-F.toKatzLevelPForm, F.dependsOnlyOnSndLine.neg⟩⟩

instance : Sub (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm - G.toKatzLevelPForm, by
    rw [sub_eq_add_neg]; exact F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine.neg⟩⟩

instance : SMul R (KatzGamma0Form R p k) :=
  ⟨fun c F => ⟨c • F.toKatzLevelPForm, F.dependsOnlyOnSndLine.smul c⟩⟩

instance : AddCommGroup (KatzGamma0Form R p k) where
  add_assoc F G H := by ext1; simp [add_assoc]
  zero_add F := by ext1; simp
  add_zero F := by ext1; simp
  add_comm F G := by ext1; simp [add_comm]
  neg_add_cancel F := by ext1; simp
  sub_eq_add_neg F G := by ext1; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzGamma0Form R p k) where
  one_smul F := by ext1; simp
  mul_smul a b F := by ext1; simp [mul_smul]
  smul_zero a := by ext1; simp
  smul_add a F G := by ext1; simp
  add_smul a b F := by ext1; simp [add_smul]
  zero_smul F := by ext1; simp

end KatzGamma0Form

end ModularCurve


end
