module

public import Def.Analysis.SpecialFunctions.Exponential
public section


class Exp (α : Type u) extends AddCommGroup α, DivInvMonoid α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y
  exp_zero : exp 0 = 1
  exp_neg (x : α) : exp (-x) = (exp x)⁻¹

/--
typeclass for ℝ ℝ* ℂ, List.Vector α, Tensor α
-/
class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

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

