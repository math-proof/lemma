import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Theorem.Analysis.SpecialFunctions.Exponential.Part3
open Filter Hyperreal Int


/--
typeclass for ℝ ℝ* ℂ, List.Vector α, Tensor α
-/
class ExpNeZero (α : Type u) extends Exp α where
  exp_ne_zero (x : α) : exp x ≠ 0

