import Mathlib.Tactic
import Mathlib.Analysis.Real.Hyperreal
open Filter

noncomputable def Hyperreal.exp (x : ℝ*) : ℝ* :=
  x.map Real.exp

theorem Hyperreal.exp_add (x y : ℝ*) : exp (x + y) = exp x * exp y := by
  refine Germ.inductionOn₂ x y fun f g => ?_
  -- rw [Germ.map]
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_add]

@[simp]
theorem Hyperreal.exp_zero : exp 0 = 1 := by
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_zero]

/-- the exponential function as a monoid hom from `Multiplicative ℝ*` to `ℝ*` -/
@[simps]
noncomputable def Hyperreal.expMonoidHom : MonoidHom (Multiplicative ℝ*) ℝ* :=
  { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }


theorem Hyperreal.exp_neg x : exp (-x) = (exp x)⁻¹ := by
  refine Germ.inductionOn x fun f => ?_
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_neg]

theorem Hyperreal.exp_ne_zero x : exp x ≠ 0 := by
  refine Germ.inductionOn x fun f => ?_
  -- rw [Germ.map]
  intro h
  obtain ⟨n, hn⟩ := Filter.nonempty_of_mem (Germ.coe_eq.mp h)
  simp at hn

theorem Hyperreal.exp_pos x : exp x > 0 := by
    refine Germ.inductionOn x fun f => ?_
    -- show 0 < Germ.ofFun (fun n => Real.exp (f n))
    apply Germ.coe_lt.mpr ∘ Eventually.of_forall
    simp [Real.exp_pos]


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
class ExpPos (α : Type u) extends ExpRing α, PartialOrder α where
  exp_pos (x : α) : exp x > 0

noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos

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
    refine Germ.inductionOn x fun f => ?_
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_div_self]


class LogPos (α : Type u) extends Log α, ExpPos α where
  log_mul (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x * y) = log x + log y
  log_div (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x / y) = log x - log y
  log_exp (x : α) : log (exp x) = x

noncomputable instance : LogPos ℝ where
  log_mul h_x h_y := Real.log_mul h_x h_y
  log_div h_x h_y := Real.log_div h_x h_y
  log_exp x := Real.log_exp x

noncomputable instance : LogPos ℝ* where
  log_mul {x y : ℝ*} h_x h_y := by
    revert h_x h_y
    refine Germ.inductionOn₂ x y fun f g h_x h_y => ?_
    have hx_event : {t | f t ≠ 0} ∈ hyperfilter ℕ := by
      apply Ultrafilter.eventually_not.mpr
      apply mt Germ.coe_eq.mpr
      exact h_x
    have hy_event : {t | g t ≠ 0} ∈ hyperfilter ℕ := by
      apply Ultrafilter.eventually_not.mpr
      apply mt Germ.coe_eq.mpr
      exact h_y
    apply Germ.coe_eq.mpr
    filter_upwards [hx_event, hy_event] with n hn gn
    apply Real.log_mul hn gn

  log_div {x y : ℝ*} := by
    refine Germ.inductionOn₂ x y fun f g => ?_
    intro h_x h_y
    have hx_event : ∀ᶠ n in hyperfilter ℕ, f n ≠ 0 := by
      apply Ultrafilter.eventually_not.mpr
      apply mt Germ.coe_eq.mpr
      exact h_x
    have hy_event : ∀ᶠ n in hyperfilter ℕ, g n ≠ 0 := by
      apply Ultrafilter.eventually_not.mpr
      apply mt Germ.coe_eq.mpr
      exact h_y
    have h_event : ∀ᶠ n in hyperfilter ℕ, f n ≠ 0 ∧ g n ≠ 0 :=
      hx_event.and hy_event
    apply Germ.coe_eq.mpr
    filter_upwards [h_event] with n hn
    exact Real.log_div hn.1 hn.2

  log_exp x := by
    refine Germ.inductionOn x fun f => ?_
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_exp]

export Exp (exp)
export Log (log)
