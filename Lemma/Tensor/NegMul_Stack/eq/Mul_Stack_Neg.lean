import Lemma.Tensor.Mul_Neg.eq.NegMul
import Lemma.Tensor.NegStack.eq.Stack_Neg
import sympy.tensor.stack
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.NegMul_Stack.eq.Mul_Stack_Neg |
| comm | Tensor.Mul_Stack_Neg.eq.NegMul_Stack |
-/
@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (X : Tensor α (n :: s))
  (a : Fin n → Tensor α s) :
-- imply
  -(X * [i < n] a i) = X * [i < n] (-a i) := by
-- proof
  rw [NegMul.eq.Mul_Neg, NegStack.eq.Stack_Neg]


@[main, comm]
private lemma Fun
  [Mul α] [HasDistribNeg α]
-- given
  (X : Tensor α (n :: s))
  (a : ℕ → Tensor α s) :
-- imply
  -(X * [i < n] a i) = X * [i < n] (-a i) :=
-- proof
  main X (fun i => a i)


-- created on 2026-09-02
