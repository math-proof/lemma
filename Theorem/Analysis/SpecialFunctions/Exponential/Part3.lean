import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Instance.Analysis.SpecialFunctions.Exponential
open Filter Hyperreal Int


@[simp]
theorem Hyperreal.exp.rfl (x : ℝ*) : Exp.exp x = x.exp := by rfl

