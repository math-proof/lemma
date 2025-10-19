import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
open List Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨0, by grind⟩ d).permute ⟨d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [Permute.eq.Ite (d := ⟨d, by simp [LengthPermute.eq.Length]; omega⟩) (k := -d)]
  simp
  split_ifs with h_sub h_pos h_j_0
  repeat omega
  .
    sorry
  .
    sorry


-- created on 2025-10-19
