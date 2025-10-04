import Mathlib.Tactic
import Mathlib.Analysis.Real.Hyperreal
open Filter

class Exp (α : Type u) extends Add α, Mul α, Zero α, One α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y
  exp_zero : exp 0 = 1

noncomputable instance : Exp ℝ where
  exp := Real.exp
  exp_add := Real.exp_add
  exp_zero := Real.exp_zero

noncomputable instance : Exp ℂ where
  exp := Complex.exp
  exp_add := Complex.exp_add
  exp_zero := Complex.exp_zero

noncomputable instance : Exp ℝ* where
  exp x := x.map Real.exp
  exp_add x y := by
    refine Germ.inductionOn₂ x y fun f g => ?_
    -- rw [Germ.map]
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.exp_add]
  exp_zero := by
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.exp_zero]

class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero x := by
    refine Germ.inductionOn x fun f => ?_
    -- rw [Germ.map]
    intro h
    obtain ⟨n, hn⟩ := Filter.nonempty_of_mem (Germ.coe_eq.mp h)
    simp at hn

class ExpPos (α : Type u) extends ExpNeZero α, LT α where
  exp_pos (x : α) : exp x > 0

noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos

noncomputable instance : ExpPos ℝ* where
  exp_pos x := by
    refine Germ.inductionOn x fun f => ?_
    -- show 0 < Germ.ofFun (fun n => Real.exp (f n))
    apply Germ.coe_lt.mpr ∘ Eventually.of_forall
    simp [Real.exp_pos]

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
