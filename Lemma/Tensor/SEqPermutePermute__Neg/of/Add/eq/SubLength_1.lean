import Lemma.Tensor.Permute.eq.Ite
open Tensor


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
  (X.permute ⟨i + d, by omega⟩ (-d)).permute ⟨i, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d
  have h_i_eq : i = s.length - (1 + d) := by omega
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
  simp
  split_ifs with h_sub h_pos
  ·
    omega
  ·
    sorry
  ·
    sorry


-- created on 2025-10-26
