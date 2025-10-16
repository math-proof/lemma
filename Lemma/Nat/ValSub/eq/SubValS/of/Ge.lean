import Lemma.Nat.ModAddSub.eq.Sub.of.Ne_0
import Lemma.Algebra.Ne_0
open Algebra Nat


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i ≥ j) :
-- imply
  (i - j).val = i.val - j.val := by
-- proof
  rw [Fin.sub_def]
  simp
  rw [ModAddSub.eq.Sub.of.Ne_0 (by simp_all) (by simp) (by simp)]


-- created on 2025-06-21
