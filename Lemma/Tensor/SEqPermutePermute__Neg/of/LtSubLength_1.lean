import Lemma.Tensor.Permute.eq.Ite
open Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨d, by grind⟩ (-d)).permute ⟨0, by simp; omega⟩ d ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  split_ifs with h_sub
  ·
    omega
  ·
    sorry


-- created on 2025-10-26
