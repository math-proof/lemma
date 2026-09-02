import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetNeg.eq.NegGet
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.NegStack.eq.Stack_Neg |
| comm | Tensor.Stack_Neg.eq.NegStack |
| fun | Tensor.NegStack.eq.Stack_Neg.fun |
| comm.fun | Tensor.Stack_Neg.eq.NegStack.fun |
-/
@[main, comm]
private lemma main
  [Neg α]
-- given
  (f : Fin n → Tensor α s) :
-- imply
  -[i < n] f i = [i < n] (-f i) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  have hN := GetNeg.eq.NegGet (X := ([i < n] f i : Tensor α (n :: s))) ⟨i, by simp [Tensor.length]⟩
  have hf := EqGetStack.fin f i
  have hnf := EqGetStack.fin (fun i => -f i) i
  refine hN.trans ?_
  exact (congrArg Neg.neg hf).trans hnf.symm


@[main, comm]
private lemma Fun
  [Neg α]
-- given
  (f : ℕ → Tensor α s) :
-- imply
  -[i < n] f i = [i < n] (-f i) :=
-- proof
  main fun i => f i


-- created on 2026-09-02
