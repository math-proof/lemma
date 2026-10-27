import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Def.Analysis.SpecialFunctions.Exponential
open Filter Hyperreal Int


theorem Hyperreal.exp_add (x y : ℝ*) : exp (x + y) = exp x * exp y := by
  refine Germ.inductionOn₂ x y fun x y => ?_
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_add]

@[simp]
theorem Hyperreal.exp_zero : exp 0 = 1 := by
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_zero]

