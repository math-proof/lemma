import stdlib.List
import Lemma.Nat.EqAdd_Sub.of.Ge
open Nat


@[main]
private lemma main
  {s : List ℕ}
  {slices : List Slice}
-- given
  (h : slices.length ≤ s.length) :
-- imply
  (slices.enumerate.map (fun args ↦ args.snd.length s[args.fst]) ++ s.drop slices.length).length = s.length := by
-- proof
  simp [List.enumerate]
  apply EqAdd_Sub.of.Ge h


-- created on 2025-06-02
