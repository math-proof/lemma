module
public import Def.ModularCurve_EMD
public import Def.ModularCurve_TatePoint
set_option autoImplicit false
open scoped Classical


public section

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.B3

open ModularCurve.TatePoint

def integralO : Subring H where
  carrier := {x : H | 0 ≤ x.orderTop}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, HahnSeries.orderTop_zero]
    exact le_top
  one_mem' := by
    simp only [Set.mem_setOf_eq, HahnSeries.orderTop_one, le_refl]
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, HahnSeries.orderTop_mul]
    exact add_nonneg ha hb
  neg_mem' := fun {a} ha => by
    simpa only [Set.mem_setOf_eq, HahnSeries.orderTop_neg] using ha

def resO : integralO →+* Qbar where
  toFun x := (x : H).coeff 0
  map_one' := by
    rw [OneMemClass.coe_one, HahnSeries.coeff_one, if_pos rfl]
  map_mul' x y := by
    rw [Subring.coe_mul]
    exact coeff_zero_mul_of_integral (mem_integralO.mp x.2) (mem_integralO.mp y.2)
  map_zero' := by
    rw [ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  map_add' x y := by
    rw [Subring.coe_add, HahnSeries.coeff_add]

def IntegralCoeffs (W : WeierstrassCurve H) : Prop :=
  0 ≤ W.a₁.orderTop ∧ 0 ≤ W.a₂.orderTop ∧ 0 ≤ W.a₃.orderTop ∧
    0 ≤ W.a₄.orderTop ∧ 0 ≤ W.a₆.orderTop

def specialFibre (W : WeierstrassCurve H) : WeierstrassCurve Qbar :=
  ⟨W.a₁.coeff 0, W.a₂.coeff 0, W.a₃.coeff 0, W.a₄.coeff 0, W.a₆.coeff 0⟩

def sU (q : ℚ) : Hˣ where
  val := HahnSeries.single q 1
  inv := HahnSeries.single (-q) 1
  val_inv := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one]
  inv_val := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]

def scaleVC (j₀ : Qbar) : VariableChange H :=
  if j₀ = 0 then
    ⟨sU (2 / 12), -(jNear 0 - 1728) ^ 2 / 12, -(jNear 0 - 1728) / 2, (jNear 0 - 1728) ^ 3 / 24⟩
  else if j₀ = 1728 then ⟨sU (9 / 12), 0, 0, 0⟩
  else 1

def goodModel (j₀ : Qbar) : WeierstrassCurve H := scaleVC j₀ • nearCurve j₀

end ModularCurve.B3

end
