import sympy.sets.fancyset
import Lemma.Hyperreal.UFn.of.All_Ufn
import Lemma.Int.Abs.eq.Max_Neg
open Filter Hyperreal Int


noncomputable def Hyperreal.exp (x : ℝ*) : ℝ* :=
  x.map Real.exp

theorem Hyperreal.exp_add (x y : ℝ*) : exp (x + y) = exp x * exp y := by
  refine Germ.inductionOn₂ x y fun x y => ?_
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_add]

@[simp]
theorem Hyperreal.exp_zero : exp 0 = 1 := by
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_zero]

/-- the exponential function as a monoid hom from `Multiplicative ℝ*` to `ℝ*` -/
@[simps]
noncomputable def Hyperreal.expMonoidHom : MonoidHom (Multiplicative ℝ*) ℝ* :=
  {
    toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add]
  }

theorem Hyperreal.exp_neg x : exp (-x) = (exp x)⁻¹ := by
  apply UFn.of.All_Ufn x
  intro x
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_neg]

theorem Hyperreal.exp_ne_zero x : exp x ≠ 0 := by
  apply UFn.of.All_Ufn x
  intro x h
  obtain ⟨n, hn⟩ := nonempty_of_mem (Germ.coe_eq.mp h)
  simp at hn

theorem Hyperreal.exp_pos x : exp x > 0 := by
  apply UFn.of.All_Ufn x
  intro x
  apply Germ.coe_lt.mpr ∘ Eventually.of_forall
  simp [Real.exp_pos]

-- copied from Mathlib\Analysis\Complex\Exponential.lean
theorem Real.add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

-- copied from Mathlib\Analysis\Complex\Exponential.lean
theorem Real.add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

theorem Hyperreal.add_one_le_exp_of_nonneg (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  revert hx
  apply UFn.of.All_Ufn x
  intro x hx
  apply Germ.coe_le.mpr
  filter_upwards [Germ.coe_nonneg.mp hx] with _ hn
  exact Real.add_one_le_exp_of_nonneg hn

@[mono, gcongr]
theorem Hyperreal.exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2 (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

theorem Hyperreal.exp_injective : Function.Injective Hyperreal.exp :=
  exp_strictMono.injective

theorem Hyperreal.exp_eq_exp : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

class Exp (α : Type u) extends AddCommGroup α, DivInvMonoid α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y
  exp_zero : exp 0 = 1
  exp_neg (x : α) : exp (-x) = (exp x)⁻¹

noncomputable instance : Exp ℝ where
  exp := Real.exp
  exp_add := Real.exp_add
  exp_zero := Real.exp_zero
  exp_neg := Real.exp_neg

noncomputable instance : Exp ℂ where
  exp := Complex.exp
  exp_add := Complex.exp_add
  exp_zero := Complex.exp_zero
  exp_neg := Complex.exp_neg

noncomputable instance : Exp ℝ* where
  exp := Hyperreal.exp
  exp_add := Hyperreal.exp_add
  exp_zero := Hyperreal.exp_zero
  exp_neg := Hyperreal.exp_neg


/--
typeclass for ℝ ℝ* ℂ, List.Vector α, Tensor α
-/
class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero := Hyperreal.exp_ne_zero

/--
typeclass for ℝ ℝ* ℂ, where GroupWithZero is a requisite
-/
class ExpRing (α : Type u) extends ExpNeZero α, DivisionSemiring α

/--
typeclass for ℝ ℝ* only
-/
class ExpPos (α : Type u) extends ExpRing α, LinearOrder α where
  exp_pos (x : α) : exp x > 0
  exp_eq_exp : exp x = exp y ↔ x = y
  exp_lt_exp : exp x < exp y ↔ x < y

noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos
  exp_eq_exp := Real.exp_eq_exp
  exp_lt_exp := Real.exp_lt_exp

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos
  exp_eq_exp := Hyperreal.exp_eq_exp
  exp_lt_exp := Hyperreal.exp_strictMono.lt_iff_lt

class Log (α : Type u) extends Zero α, One α, Div α where
  log : α → α
  log_zero : log 0 = 0
  log_one : log 1 = 0
  log_div_self (x : α) : log (x / x) = 0

noncomputable instance : Log ℝ where
  log := Real.log
  log_zero := Real.log_zero
  log_one := Real.log_one
  log_div_self := Real.log_div_self

noncomputable instance : Log ℂ where
  log := Complex.log
  log_zero := Complex.log_zero
  log_one := Complex.log_one
  log_div_self := Complex.log_div_self

noncomputable instance : Log ℝ* where
  log x := x.map Real.log
  log_zero := by
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_zero]
  log_one := by
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_one]
  log_div_self x := by
    apply UFn.of.All_Ufn x
    intro x
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_div_self]


class LogPos (α : Type u) extends Log α, ExpPos α where
  log_mul (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x * y) = log x + log y
  log_div (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x / y) = log x - log y
  log_exp (x : α) : log (exp x) = x
  exp_log_eq_abs (h : x ≠ 0) : exp (log x) = |x|

noncomputable instance : LogPos ℝ where
  log_mul h_x h_y := Real.log_mul h_x h_y
  log_div h_x h_y := Real.log_div h_x h_y
  log_exp x := Real.log_exp x
  exp_log_eq_abs := Real.exp_log_eq_abs

noncomputable instance : LogPos ℝ* where
  log_mul {x y} := by
    refine Germ.inductionOn₂ x y fun x y h_x h_y => ?_
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_x), Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_y)] with _ hn gn
    exact Real.log_mul hn gn

  log_div {x y} := by
    refine Germ.inductionOn₂ x y fun x y => ?_
    intro h_x h_y
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_x), Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_y)] with _ hn gn
    exact Real.log_div hn gn

  log_exp x := by
    apply UFn.of.All_Ufn x
    intro x
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_exp]

  exp_log_eq_abs {x} := by
    apply UFn.of.All_Ufn x
    intro x h
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h)] with _ hn
    simp [Real.exp_log_eq_abs hn]
    apply Abs.eq.Max_Neg


export Exp (exp)
export Log (log)
