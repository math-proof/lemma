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


class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero := Hyperreal.exp_ne_zero

class ExpPos (α : Type u) extends ExpNeZero α, PartialOrder α, DivisionSemiring α where
  exp_pos (x : α) : exp x > 0

noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos

class Log (α : Type u) where
  log : α → α

noncomputable instance : Log ℝ where
  log := Real.log

noncomputable instance : Log ℂ where
  log := Complex.log

noncomputable instance : Log ℝ* where
  log x := x.map Real.log


export Exp (exp)
export Log (log)
