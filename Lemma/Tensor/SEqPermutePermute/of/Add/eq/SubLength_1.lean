import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
open List Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  split_ifs with h_sub h_pos h_j_0 h_eq_d
  repeat omega
  .
    sorry
  .
    simp at h_eq_d
    rw [LengthPermute.eq.Length] at h_eq_d
    contradiction


-- created on 2025-10-19
