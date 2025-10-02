import Mathlib.Tactic

class Exp (α : Type u) extends Add α, Mul α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y

noncomputable instance : Exp ℝ where
  exp := Real.exp
  exp_add := Real.exp_add

noncomputable instance : Exp ℂ where
  exp := Complex.exp
  exp_add := Complex.exp_add

class Log (α : Type u) where
  log : α → α


export Exp (exp)
