import Lemma.Vector.ExpAdd.eq.MulExpS
import Lemma.Vector.Softmax.eq.Div_SumExp
import Lemma.Vector.SumMul.eq.MulSum
import sympy.tensor.functions
open Vector


@[main]
private lemma main
  [ExpGroup α]
-- given
  (x : List.Vector α n)
  (δ : α) :
-- imply
  (x + δ).softmax = x.softmax := by
-- proof
  simp [Softmax.eq.Div_SumExp]
  rw [ExpAdd.eq.MulExpS.scalar]
  rw [SumMul.eq.MulSum]
  sorry


-- created on 2025-11-30
