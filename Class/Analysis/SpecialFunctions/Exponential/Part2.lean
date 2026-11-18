module

public import Class.Analysis.SpecialFunctions.Exponential
public section
open Filter Hyperreal Int

/--
typeclass for ℝ ℝ* ℂ, List.Vector α, Tensor α
-/
class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

