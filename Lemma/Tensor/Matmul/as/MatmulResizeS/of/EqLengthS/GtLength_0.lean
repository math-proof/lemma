import Lemma.Bool.HEq.of.SEq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Tensor.SEqFromVectorS.of.SEq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqToVectorS.of.SEq
import sympy.tensor.tensor
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, comm, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > 0)
  (h_length : s.length = s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  let X' : Tensor α ((s[0] ⊔ s'[0]) :: s.tail ++ [m, n]) := cast (congrArg (Tensor α) (by
    rw [SetAppend.eq.Append_Set.of.GtLength (by grind)]
    congr 1
    simp
    rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
  )) (X.resize ⟨0, by grind⟩ (s[0] ⊔ s'[0]))
  let Y' : Tensor α ((s[0] ⊔ s'[0]) :: s'.tail ++ [n, k]) := cast (congrArg (Tensor α) (by
    rw [SetAppend.eq.Append_Set.of.GtLength (by grind)]
    congr 1
    simp
    rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
  )) (Y.resize ⟨0, by grind⟩ (s[0] ⊔ s'[0]))
  X.matmul Y (by grind) ≃ X'.matmul Y' (by grind) := by
-- proof
  intro X' Y'
  simp [X', Y']
  unfold matmul
  simp
  match s, s' with
  | s₀ :: s, s'₀ :: s' =>
    simp
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [broadcast_shape]
      split_ifs with h h
      ·
        simp
        grind
      ·
        simp
        grind
      ·
        simp
    ·
      simp [broadcast_shape]
      split_ifs with h h
      ·
        simp
        grind
      ·
        simp
        grind
      ·
        simp
    ·
      apply SEqFromVectorS.of.SEq
      constructor
      ·
        simp
      ·
        congr 1
        ·
          simp
        ·
          apply HEq.of.SEq
          apply SEqToVectorS.of.SEq
          symm
          apply SEqResize_0.of.Eq_Get_0.GtLength_0
          .
            simp
          .
            simp
        ·
          apply HEq.of.SEq
          apply SEqToVectorS.of.SEq
          symm
          apply SEqResize_0.of.Eq_Get_0.GtLength_0
          .
            simp
          .
            simp


-- created on 2026-07-17
