import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Instance.Analysis.SpecialFunctions.Exponential.Part2
open Filter Hyperreal Int


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

