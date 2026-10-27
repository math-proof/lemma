import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Theorem.Analysis.SpecialFunctions.Exponential.Part2
open Filter Hyperreal Int


class Exp (α : Type u) extends AddCommGroup α, DivInvMonoid α where
  exp : α → α
  exp_add (x y : α) : exp (x + y) = exp x * exp y
  exp_zero : exp 0 = 1
  exp_neg (x : α) : exp (-x) = (exp x)⁻¹

