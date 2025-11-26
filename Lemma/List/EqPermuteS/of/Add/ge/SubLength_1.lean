import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
open List Int Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d ≥ s.length - 1) :
-- imply
  s.permute i d = s.permute i (s.length - 1 - i : ℕ) := by
-- proof
  repeat rw [Permute.eq.Append_AppendRotateTakeDrop]
  simp_all [show (s.length - 1 - i + 1) = s.length - i by omega]
  rw [Drop.eq.Nil.of.LeLength (i := i + (d + 1)) (by simp; omega)]
  simp
  omega


@[main]
private lemma int
  {s : List α}
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h : i + d ≥ s.length - 1) :
-- imply
  s.permute i d = s.permute i (s.length - 1 - i) := by
-- proof
  match d with
  | Int.ofNat d =>
    have := main (i := i) (d := d) (by simp_all; omega)
    simp_all
    rw [CoeSub.eq.SubCoeS.of.Ge]
    repeat grind
  | Int.negSucc d =>
    have h_i := i.isLt
    rw [NegSucc.eq.NegAdd_1] at h
    simp at h
    linarith


-- created on 2025-06-07
-- updated on 2025-10-31
