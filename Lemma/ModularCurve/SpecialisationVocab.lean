import Def.ModularCurve_EMD
import Def.ModularCurve_TatePoint

set_option autoImplicit false

open scoped Classical

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.B3

open ModularCurve.TatePoint

theorem leadingCoeff_eq_coeff_order {x : H} (hx : x ≠ 0) :
    x.leadingCoeff = x.coeff x.order := by
  rw [HahnSeries.leadingCoeff_of_ne_zero hx]
  congr 1
  rw [WithTop.untop_eq_iff]
  exact (HahnSeries.order_eq_orderTop_of_ne_zero hx).symm

theorem coeff_zero_mul_of_integral {x y : H} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  rcases hx.lt_or_eq with h1 | h1
  · have hx0 : x.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop h1
    have hxy : (0 : WithTop ℚ) < (x * y).orderTop := by
      rw [HahnSeries.orderTop_mul]
      exact lt_of_lt_of_le h1 (le_add_of_nonneg_right hy)
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hxy, hx0, zero_mul]
  · rcases hy.lt_or_eq with h2 | h2
    · have hy0 : y.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop h2
      have hxy : (0 : WithTop ℚ) < (x * y).orderTop := by
        rw [HahnSeries.orderTop_mul]
        exact lt_of_lt_of_le h2 (le_add_of_nonneg_left hx)
      rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hxy, hy0, mul_zero]
    · have hx0 : x ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [← h1]; simp)
      have hy0 : y ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [← h2]; simp)
      have hordx : x.order = 0 := by
        have h : (x.order : WithTop ℚ) = 0 :=
          (HahnSeries.order_eq_orderTop_of_ne_zero hx0).trans h1.symm
        exact_mod_cast h
      have hordy : y.order = 0 := by
        have h : (y.order : WithTop ℚ) = 0 :=
          (HahnSeries.order_eq_orderTop_of_ne_zero hy0).trans h2.symm
        exact_mod_cast h
      have key := HahnSeries.coeff_mul_order_add_order x y
      rw [hordx, hordy, add_zero] at key
      rw [key, leadingCoeff_eq_coeff_order hx0, leadingCoeff_eq_coeff_order hy0,
        hordx, hordy]

theorem orderTop_pow_nonneg {x : H} (hx : 0 ≤ x.orderTop) (k : ℕ) :
    0 ≤ (x ^ k : H).orderTop := by
  induction k with
  | zero => simp [HahnSeries.orderTop_one]
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul]
    exact add_nonneg ih hx

theorem coeff_zero_pow_of_integral {x : H} (hx : 0 ≤ x.orderTop) (k : ℕ) :
    (x ^ k : H).coeff 0 = x.coeff 0 ^ k := by
  induction k with
  | zero => simp [HahnSeries.coeff_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, coeff_zero_mul_of_integral (orderTop_pow_nonneg hx k) hx, ih]

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

theorem mem_integralO {x : H} : x ∈ integralO ↔ 0 ≤ x.orderTop := by exact Iff.rfl

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

@[simp] theorem resO_apply (x : integralO) : resO x = (x : H).coeff 0 := rfl

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

@[simp] theorem val_sU (q : ℚ) : ((sU q : Hˣ) : H) = HahnSeries.single q 1 := rfl

@[simp] theorem val_inv_sU (q : ℚ) : (((sU q)⁻¹ : Hˣ) : H) = HahnSeries.single (-q) 1 := rfl

def scaleVC (j₀ : Qbar) : VariableChange H :=
  if j₀ = 0 then
    ⟨sU (2 / 12), -(jNear 0 - 1728) ^ 2 / 12, -(jNear 0 - 1728) / 2, (jNear 0 - 1728) ^ 3 / 24⟩
  else if j₀ = 1728 then ⟨sU (9 / 12), 0, 0, 0⟩
  else 1

def goodModel (j₀ : Qbar) : WeierstrassCurve H := scaleVC j₀ • nearCurve j₀

theorem scaleVC_zero : scaleVC 0 =
    ⟨sU (2 / 12), -(jNear 0 - 1728) ^ 2 / 12, -(jNear 0 - 1728) / 2,
      (jNear 0 - 1728) ^ 3 / 24⟩ := by
  rw [scaleVC, if_pos rfl]

theorem scaleVC_1728 : scaleVC 1728 = ⟨sU (9 / 12), 0, 0, 0⟩ := by
  rw [scaleVC, if_neg (by norm_num), if_pos rfl]

theorem scaleVC_of_ne {j₀ : Qbar} (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) : scaleVC j₀ = 1 := by
  rw [scaleVC, if_neg h0, if_neg h1728]

theorem goodModel_eq_nearCurve {j₀ : Qbar} (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) :
    goodModel j₀ = nearCurve j₀ := by
  rw [goodModel, scaleVC_of_ne h0 h1728, one_smul]

end ModularCurve.B3

end
