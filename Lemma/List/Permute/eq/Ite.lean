import stdlib.List
import Lemma.Algebra.NegSucc.eq.NegAdd_1
open Algebra


@[main]
private lemma main
-- given
  (a : List α)
  (i : Fin a.length)
  (d : ℤ) :
-- imply
  a.permute i d =
    if d < 0 then
      let d := (-d).toNat
      a.take (i - d) ++ a[i] :: a.slice (i - d) i ++ a.drop (i + 1)
    else
      let d := (d + 1).toNat
      a.take i ++ a.slice (i + 1) (i + d) ++ a[i] :: a.drop (i + d) := by
-- proof
  simp [List.permute]
  split_ifs with h
  ·
    match d with
    | .ofNat d =>
      contradiction
    | .negSucc d =>
      simp_all
      rw [NegSucc.eq.NegAdd_1]
      simp
  ·
    match d with
    | .ofNat d =>
      simp_all
    | .negSucc d =>
      simp_all


-- created on 2025-06-07
