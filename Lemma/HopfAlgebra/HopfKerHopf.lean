-- Carved: defs+theorems -> Def.HopfAlgebra_HopfKerHopf; instances remain here
import Mathlib
import Lemma.HopfAlgebra.HopfKer
import Def.HopfAlgebra_HopfKerHopf
import Instance.HopfAlgebra_HopfKerHopf


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct
open Coalgebra

universe u v w

namespace HopfAlgebra.HopfKerHopf

section AntiCoalgebra

open WithConv

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [HopfAlgebra R A]


end

end AntiCoalgebra

section MapAntipode

open WithConv

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B]


end MapAntipode

section Stability

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)


end Stability

section Structure

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)
variable [Module.Flat R A] [Module.Flat R B] [Module.Flat R ↥(hopfKer π)]
variable [Coalgebra.IsCocomm R A]

theorem comul_def (s : ↥(hopfKer π)) : Coalgebra.comul (R := R) s = comulK π s := rfl
theorem counit_coe (s : ↥(hopfKer π)) : Coalgebra.counit (R := R) s = Coalgebra.counit (R := R) (s : A) := by
  change counitK π s = Coalgebra.counit (R := R) (s : A)
  exact counitK_apply π s
@[simp] theorem ι₂_comul (s : ↥(hopfKer π)) : ι₂ π (Coalgebra.comul (R := R) s) = Coalgebra.comul (R := R) (s : A) := by
  rw [comul_def]
  exact ι₂_comulK π s

theorem map_val_val_comul (s : ↥(hopfKer π)) :
    TensorProduct.map (valL π) (valL π) (Coalgebra.comul (R := R) s) = Coalgebra.comul (R := R) (s : A) := by
  rw [← ι₂_eq_map, ι₂_comul]
@[simp] theorem coe_antipode (s : ↥(hopfKer π)) : ((antipode R s : ↥(hopfKer π)) : A) = antipode R (s : A) := by
  change ((antipodeK π s : ↥(hopfKer π)) : A) = antipode R (s : A)
  exact coe_antipodeK π s
noncomputable def hopfKerVal : ↥(hopfKer π) →ₐc[R] A :=
  { (hopfKer π).val with
    map_smul' := fun r x => by simp
    counit_comp := rfl
    map_comp_comul := by
      ext s
      change TensorProduct.map (valL π) (valL π) (Coalgebra.comul (R := R) s) = Coalgebra.comul (R := R) (s : A)
      exact map_val_val_comul π s }

@[simp] theorem hopfKerVal_apply (s : ↥(hopfKer π)) : hopfKerVal π s = (s : A) := rfl

theorem hopfKerVal_injective : Function.Injective (hopfKerVal π) := Subtype.val_injective

end Structure

end HopfAlgebra.HopfKerHopf

namespace HopfAlgebra

export HopfKerHopf (hopfKerVal hopfKerVal_apply hopfKerVal_injective map_val_val_comul counit_coe coe_antipode
  antipode_mem map_antipode comul_antipode)

end HopfAlgebra

section SanityTests
open HopfAlgebra
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)
variable [Coalgebra.IsCocomm R A] [Module.Flat R A] [Module.Flat R B] [Module.Flat R ↥(hopfKer π)]

noncomputable example : HopfAlgebra R ↥(hopfKer π) := inferInstance
example : Coalgebra.IsCocomm R ↥(hopfKer π) := inferInstance
example : (Bialgebra.toCoalgebra : Coalgebra R ↥(hopfKer π)) = HopfAlgebra.HopfKerHopf.instCoalgebra π := rfl
example (s : ↥(hopfKer π)) : Coalgebra.counit (R := R) s = Coalgebra.counit (R := R) (s : A) := rfl
example (s : ↥(hopfKer π)) : ((antipode R s : ↥(hopfKer π)) : A) = antipode R (s : A) := coe_antipode π s
example (s : ↥(hopfKer π)) :
    TensorProduct.map (hopfKerVal π).toLinearMap (hopfKerVal π).toLinearMap (Coalgebra.comul (R := R) s)
      = Coalgebra.comul (R := R) (s : A) := map_val_val_comul π s

example (P : ∀ (C : Type v) [CommRing C] [Bialgebra R C] [Coalgebra.IsCocomm R C], Prop)
    (h : ∀ (C : Type v) [CommRing C] [Bialgebra R C] [Coalgebra.IsCocomm R C], P C) : P ↥(hopfKer π) := h _
example (P : ∀ (C : Type v) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C], Prop)
    (h : ∀ (C : Type v) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C], P C) : P ↥(hopfKer π) := h _
end SanityTests
