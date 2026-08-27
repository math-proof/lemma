import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.LengthSet.eq.Length
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Tensor.Resize_0.as.AppendCast_Repeat_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqAppend.of.Eq_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
open Bool List Nat Tensor


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_d : d < s.length)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat ⟨d, h_d⟩ n ≃ X.resize ⟨d, h_d⟩ (n * s[d]) := by
-- proof
  induction d generalizing X s with
  | zero =>
    cases s with
    | nil =>
      exact absurd h_d (Nat.not_lt_zero 0)
    | cons k s =>
      have h0 : (k :: s).length > 0 := Nat.succ_pos _
      apply SEq.symm
      apply SEq.trans (Resize_0.as.AppendCast_Repeat_0.of.GtLength_0 h0 X (n * k))
      apply SEq.trans (SEqAppend.of.Eq_0.cons (by simp) _ _)
      apply SEqCast.of.SEq.Eq (by simp [Set_0.eq.Cons_Tail.of.GtLength_0 h0])
      if h_k : k = 0 then
        subst h_k
        simp only [Nat.mul_zero, List.getElem_cons_zero]
        apply SEq.of.All_SEqGetS.Eq.GtLength_0
          (A := X.repeat ⟨0, h0⟩ 0) (B := X.repeat ⟨0, h_d⟩ n) (Nat.succ_pos _) rfl
        intro i
        exact Fin.elim0 i
      else
        obtain ⟨k', hk⟩ : ∃ k', k = Nat.succ k' := by
          refine ⟨k - 1, ?_⟩
          exact (Nat.succ_pred_eq_of_ne_zero h_k).symm
        subst hk
        simp only [List.getElem_cons_zero]
        rw [EqDivMul.of.Ne_0 (Nat.succ_ne_zero k') n]
  | succ d ih =>
    match s with
    | nil =>
      exact absurd h_d (Nat.not_lt_zero (d + 1))
    | cons k s₀ =>
      have h_s : ((k :: s₀).set (d + 1) (n * (k :: s₀)[d + 1])).length > 0 := by
        rw [LengthSet.eq.Length]
        grind
      apply SEq.of.All_SEqGetS.Eq.GtLength_0
        (A := X.repeat ⟨d + 1, h_d⟩ n)
        (B := X.resize ⟨d + 1, h_d⟩ (n * (k :: s₀)[d + 1])) h_s rfl
      intro i
      have h_dim : (⟨d + 1, h_d⟩ : Fin (k :: s₀).length).val > 0 := Nat.succ_pos d
      have h_d' : d < s₀.length := by
        simp only [List.length_cons] at h_d
        exact Nat.lt_of_succ_lt_succ h_d
      rw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin h_dim (by grind)]
      rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin h_dim (by grind)]
      have := ih (X := X.get ⟨i, by grind⟩) (s := s₀) h_d'
      aesop


-- created on 2026-07-30
