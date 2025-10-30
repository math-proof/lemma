import Lemma.Int.AddSub.eq.SubAdd
import Lemma.Int.CoeSub_1.eq.SubCoe_1.of.Ge_1
import Lemma.Int.EqAddSub
import Lemma.Int.Lt.of.Sub.lt.Zero
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.List.Drop.eq.Nil
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.Permute.eq.Ite
import Lemma.List.Slice.eq.Slice__Length.of.Ge_Length
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Nat.Ge_1
import Lemma.Nat.Le_Sub_1
import Lemma.Nat.LtVal
open Int List Nat


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
  have hi := Le_Sub_1 i
  have h_length := Ge_1 i
  rw [Permute.eq.Ite]
  split_ifs with h_d
  ·
    have h_ge := Ge.of.Ge.Ge h hi
    linarith
  ·
    simp at h_d
    rw [Permute.eq.Ite]
    split_ifs with h_i
    ·
      linarith
    ·
      simp
      rw [Drop.eq.Nil.of.Ge_Length (by omega)]
      rw [Slice.eq.Slice__Length.of.Ge_Length (by omega)]
      grind


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
    rw [Nat.CoeSub.eq.SubCoeS.of.Ge]
    repeat grind
  | Int.negSucc d =>
    have h_i := LtVal i
    rw [NegSucc.eq.NegAdd_1] at h
    simp at h
    linarith


-- created on 2025-06-07
-- updated on 2025-10-29
