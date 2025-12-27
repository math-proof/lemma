import Lemma.Hyperreal.SetoidExpS.of.InfinitesimalSub
import Lemma.Vector.Setoid.is.All_SetoidGetS
import sympy.vector.functions
open Vector Hyperreal


@[main]
private lemma main
  {a b : List.Vector ℝ* n}
-- given
  (h : a ≈ b) :
-- imply
  exp a ≈ exp b := by
-- proof
  simp [Exp.exp]
  apply Setoid.of.All_SetoidGetS.fin
  intro i
  simp
  apply SetoidExpS.of.InfinitesimalSub
  -- apply All_SetoidGetS.of.Setoid.fin h i
  sorry



-- created on 2025-12-24
-- updated on 2025-12-25
