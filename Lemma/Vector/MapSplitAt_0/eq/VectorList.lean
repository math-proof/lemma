import Lemma.Nat.Eq_0.of.Lt_1
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Vector.EqGetSplitAt_0'0
open Nat Vector Fin


@[main]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (f : List.Vector α s.prod → β) :
-- imply
  (v.splitAt 0).map f = ⟨[f v], by simp⟩ := by
-- proof
  ext i
  have h_i := Eq_0.of.Lt_1 (by simpa using i.isLt)
  have h_i := Eq_Fin.of.EqVal h_i
  rw [h_i]
  erw [List.Vector.get_map]
  congr
  apply EqGetSplitAt_0'0.fin


-- created on 2026-04-23
-- updated on 2026-08-24
