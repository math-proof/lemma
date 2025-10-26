import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.Tensor.Permute.eq.Ite
open Bool Tensor List


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨d, by omega⟩ (-d)).permute ⟨0, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  split_ifs with h_sub
  ·
    sorry
  ·
    have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := d) (j := 0) ⟨by omega, by omega⟩
    simp at h_permute
    apply SEqCast.of.SEq.Eq.Eq
    ·
      sorry
    ·
      sorry
    ·
      sorry


-- created on 2025-10-26
