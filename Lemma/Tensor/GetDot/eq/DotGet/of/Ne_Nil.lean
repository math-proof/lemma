import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s ≠ [])
  (X : Tensor α (n :: s))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s (by apply GeLength_1.of.Ne_Nil h_s) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  induction s generalizing n' k' n with
  | nil =>
    contradiction
  | cons k₀ ks ih =>
    match ks with
    | [] =>
      rw [GetDot.eq.DotGet.fin]
    | k₁ :: ks' =>
      simp at ih
      have ih_i := ih (Y := Y) (n := n) (i := i)
      have ih_j : ∀ j : Fin k₀,
        let Xj : Tensor α (n :: k₁ :: ks') := X.select ⟨1, by simp⟩ ⟨j, by simp⟩
        (Xj @ Y).get ⟨i, by grind⟩ ≃ (Xj.get i) @ Y := by
        intro j Xj
        specialize ih_i (X := Xj)
        exact ih_i
      simp at ih_j
      apply Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
      .
        intro j
        have h_j := j.isLt
        simp [matmul_shape, broadcast_shape] at h_j
        simp [List.TakeTake.eq.Take.of.Ge] at h_j
        have := Nat.EqMin.of.Le (show ks'.length ≤ ks'.length + 1 + 1 by omega)
        simp [this] at h_j
        have h_j : j < k₀ := by
          if h_ks : ks'.length = 0 then
            have h_ks := List.Eq_Nil.of.EqLength_0 h_ks
            simp [h_ks] at h_j
            conv_rhs at h_j => simp
            assumption
          else
            rw [List.GetAppend.eq.Get.of.GtLength (by simp; omega)] at h_j
            have : 0 < ((k₀ :: k₁ :: ks').take ks'.length).length := by
              simp
              apply Nat.Gt_0.of.Ne_0
              assumption
            rw [List.GetTake.eq.Get.of.Lt_LengthTake this] at h_j
            simp at h_j
            assumption
        have ih_j' := ih (X.get i) (n := k₀) (i := ⟨j, h_j⟩) (Y := Y)
        simp at ih_j'
        apply SEq.symm
        apply ih_j'.trans
        .
          sorry
        .
          simp [matmul_shape, broadcast_shape]
      .
        simp [matmul_shape, broadcast_shape]
        split_ifs with h₀
        .
          simp
        .
          simp_all


-- created on 2026-01-04
