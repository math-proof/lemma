import Mathlib.Tactic
import Mathlib.Analysis.Real.Hyperreal
open Filter

class Exp (α : Type u) extends Add α, Mul α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y

noncomputable instance : Exp ℝ where
  exp := Real.exp
  exp_add := Real.exp_add

noncomputable instance : Exp ℂ where
  exp := Complex.exp
  exp_add := Complex.exp_add

noncomputable instance : Exp ℝ* where
  exp x := x.map Real.exp
  exp_add x y := by
    refine Germ.inductionOn₂ x y fun f g => ?_
    rw [Germ.map]
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.exp_add]


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
