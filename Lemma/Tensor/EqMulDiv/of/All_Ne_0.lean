import Lemma.Tensor.Eq.is.EqDataS
import Def.Data.Tensor.Prod
import Instance.Data.Tensor.Defs.Part2
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.EqMulDiv.of.All_Ne_0 |
| fin 1 | Tensor.EqMulDiv.of.All_Ne_0.fin |
-/
@[path, fin 1]
private lemma main
  [GroupWithZero α]
  {B : Tensor α s}
-- given
  (h : ∀ i : Fin s.prod, B.data[i] ≠ 0)
  (A : Tensor α s) :
-- imply
  A / B * B = A := by
-- proof
  apply Eq.of.EqDataS
  ext i
  simp only [HMul.hMul, Mul.mul, HDiv.hDiv, Div.div, List.Vector.get_map₂]
  apply div_mul_cancel₀ _ (h i)


-- created on 2025-12-30
-- updated on 2026-11-20
