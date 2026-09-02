import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import sympy.tensor.stack
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.AddMulS_Stack.eq.Mul_Stack_Add |
| comm | Tensor.Mul_Stack_Add.eq.AddMulS_Stack |
-/
@[main, comm]
private lemma main
  [Mul α] [Add α] [LeftDistribClass α]
-- given
  (X : Tensor α (n :: s))
  (a b : Fin n → Tensor α s) :
-- imply
  X * [i < n] a i + X * [i < n] b i = X * [i < n] (a i + b i) := by
-- proof
  rw [← left_distrib]
  apply congrArg (fun S : Tensor α (n :: s) => X * S)
  apply Eq.of.All_EqGetS.fin
  intro i
  have hAdd := GetAdd.eq.AddGetS ([i < n] a i) ([i < n] b i) i
  have ha := EqGetStack.fin a i
  have hb := EqGetStack.fin b i
  have hab := EqGetStack.fin (fun i => a i + b i) i
  exact hAdd.trans ((congrArg₂ HAdd.hAdd ha hb).trans hab.symm)


@[main, comm]
private lemma Fun
  [Mul α] [Add α] [LeftDistribClass α]
-- given
  (X : Tensor α (n :: s))
  (a b : ℕ → Tensor α s) :
-- imply
  X * [i < n] a i + X * [i < n] b i = X * [i < n] (a i + b i) :=
-- proof
  main X (fun i => a i) (fun i => b i)


-- created on 2026-09-02
