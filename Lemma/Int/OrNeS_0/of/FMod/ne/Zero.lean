import Lemma.Bool.NotOr.is.AndNotS
import Lemma.Bool.NotNe.is.Eq
open Bool


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d ≠ 0) :
-- imply
  d ≠ 0 ∨ n ≠ 0 := by
-- proof
  by_contra h_And
  have := AndNotS.of.NotOr h_And
  let ⟨h_d, h_n⟩ := this
  have h_d := Eq.of.NotNe h_d
  have h_n := Eq.of.NotNe h_n
  rw [h_d, h_n] at h
  norm_num
  contradiction


-- created on 2025-03-30
